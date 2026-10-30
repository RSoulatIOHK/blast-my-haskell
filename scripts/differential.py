#!/usr/bin/env python3
"""Compare GHC execution with freshly generated Lean on sampled inputs."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import re
import sys
import tempfile
import time
import uuid

from pipeline import (REPO, PipelineError, atomic_write, cancel_on_termination,
                      digest, ensure_unchanged, ghc_target,
                      private_lean_environment, require, run, tool_env, transpile)

INT64_MIN = -(1 << 63)
INT64_MAX = (1 << 63) - 1
ARGUMENT_KINDS = {"int64", "integer"}
RESULT_KINDS = {"int64", "integer", "bool", "int64-list", "integer-list", "int64-pair"}
NAME = re.compile(r"^[A-Za-z][A-Za-z0-9_']*$")
MODULE = re.compile(r"^[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*$")


def boundary_vectors(arity: int) -> list[list[int]]:
    unary = [INT64_MIN, INT64_MIN + 1, -2, -1, 0, 1, 2,
             INT64_MAX - 1, INT64_MAX]
    if arity == 1:
        return [[value] for value in unary]
    if arity == 2:
        return [
            [INT64_MIN, INT64_MIN], [INT64_MIN, -1], [INT64_MIN, 0],
            [INT64_MIN, INT64_MAX], [-1, INT64_MIN], [-1, 0], [-1, 1],
            [0, INT64_MIN], [0, 0], [0, INT64_MAX], [1, -1],
            [INT64_MAX, INT64_MIN], [INT64_MAX, 1], [INT64_MAX, INT64_MAX],
        ]
    raise ValueError("Boundary generation supports unary and binary operations")


def _validate_value(value: object, kind: str, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{where} must be an integer")
    if kind == "int64" and not INT64_MIN <= value <= INT64_MAX:
        raise ValueError(f"{where} is outside the signed 64-bit range")
    return value


def load_config(path: Path) -> dict:
    config = json.loads(path.read_text())
    if config.get("schemaVersion") != 1:
        raise ValueError("Differential configuration schemaVersion must be 1")
    seed = config.get("seed")
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise ValueError("Differential seed must be an integer")
    suites = config.get("suites")
    if not isinstance(suites, list) or not suites:
        raise ValueError("Differential configuration must contain suites")
    seen_modules: set[str] = set()
    for suite_index, suite in enumerate(suites):
        where = f"suites[{suite_index}]"
        if not isinstance(suite, dict):
            raise ValueError(f"{where} must be an object")
        module = suite.get("module")
        if not isinstance(module, str) or not MODULE.fullmatch(module):
            raise ValueError(f"{where}.module is invalid")
        if module in seen_modules:
            raise ValueError(f"Duplicate differential module {module}")
        seen_modules.add(module)
        source = suite.get("source")
        if not isinstance(source, str) or not source.endswith(".hs"):
            raise ValueError(f"{where}.source must name a Haskell file")
        operations = suite.get("operations")
        if not isinstance(operations, list) or not operations:
            raise ValueError(f"{where} must contain operations")
        seen_functions: set[str] = set()
        for op_index, operation in enumerate(operations):
            op_where = f"{where}.operations[{op_index}]"
            function = operation.get("function") if isinstance(operation, dict) else None
            if not isinstance(function, str) or not NAME.fullmatch(function):
                raise ValueError(f"{op_where}.function is invalid")
            if function in seen_functions:
                raise ValueError(f"Duplicate operation {module}.{function}")
            seen_functions.add(function)
            arguments = operation.get("arguments")
            if (not isinstance(arguments, list) or not 1 <= len(arguments) <= 2
                    or any(kind not in ARGUMENT_KINDS for kind in arguments)):
                raise ValueError(f"{op_where}.arguments must contain one or two supported kinds")
            if operation.get("result") not in RESULT_KINDS:
                raise ValueError(f"{op_where}.result is unsupported")
            count = operation.get("randomCases", 0)
            if isinstance(count, bool) or not isinstance(count, int) or count < 0:
                raise ValueError(f"{op_where}.randomCases must be a nonnegative integer")
            if count and any(kind != "int64" for kind in arguments):
                raise ValueError(f"{op_where} requests random values for a non-Int argument")
            if operation.get("boundaries", False) and any(kind != "int64" for kind in arguments):
                raise ValueError(f"{op_where} requests Int boundaries for a non-Int argument")
            vectors = operation.get("vectors", [])
            if not isinstance(vectors, list):
                raise ValueError(f"{op_where}.vectors must be a list")
            for vector_index, vector in enumerate(vectors):
                if not isinstance(vector, list) or len(vector) != len(arguments):
                    raise ValueError(f"{op_where}.vectors[{vector_index}] has the wrong arity")
                for arg_index, (value, kind) in enumerate(zip(vector, arguments)):
                    _validate_value(value, kind,
                                    f"{op_where}.vectors[{vector_index}][{arg_index}]")
    return config


def expand_cases(config: dict, suite: dict) -> list[dict]:
    cases: list[dict] = []
    seed = config["seed"]
    module = suite["module"]
    for operation in suite["operations"]:
        groups: list[tuple[str, list[list[int]]]] = []
        vectors = operation.get("vectors", [])
        if vectors:
            groups.append(("vector", vectors))
        if operation.get("boundaries", False):
            groups.append(("boundary", boundary_vectors(len(operation["arguments"]))))
        random_count = operation.get("randomCases", 0)
        if random_count:
            material = f"{seed}\0{module}\0{operation['function']}".encode()
            operation_seed = int.from_bytes(hashlib.sha256(material).digest()[:8], "big")
            rng = random.Random(operation_seed)
            generated = [[rng.randint(INT64_MIN, INT64_MAX)
                          for _ in operation["arguments"]]
                         for _ in range(random_count)]
            groups.append(("random", generated))
        for origin, group in groups:
            for index, inputs in enumerate(group):
                cases.append({
                    "id": f"{module}.{operation['function']}.{origin}.{index:03d}",
                    "function": operation["function"],
                    "arguments": operation["arguments"],
                    "result": operation["result"],
                    "origin": origin,
                    "inputs": list(inputs),
                })
    if not cases:
        raise ValueError(f"Differential suite {module} has no cases")
    return cases


def _literal(value: int) -> str:
    return f"({value})" if value < 0 else str(value)


def _string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"').replace("\t", "\\t") + '"'


def haskell_runner(module: str, cases: list[dict]) -> str:
    lines = ["module Main where", "", f"import qualified {module} as Subject", "", "main :: IO ()", "main = do"]
    for case in cases:
        expression = "Subject." + case["function"] + " " + " ".join(
            _literal(value) for value in case["inputs"])
        lines.append(f"  putStrLn ({_string(case['id'] + chr(9))} ++ show ({expression}))")
    return "\n".join(lines) + "\n"


LEAN_RENDERERS = {
    "int64": "renderInt64",
    "integer": "renderInteger",
    "bool": "renderBool",
    "int64-list": "renderInt64List",
    "integer-list": "renderIntegerList",
    "int64-pair": "renderInt64Pair",
}


def lean_runner(module: str, cases: list[dict]) -> str:
    lines = [
        f"import GhcCoreToLean.Generated.{module}",
        "",
        "private def renderInt64 (value : Int64) : String := toString value.toInt",
        "private def renderInteger (value : Int) : String := toString value",
        'private def renderBool (value : Bool) : String := if value then "True" else "False"',
        "private def renderInt64List (values : List Int64) : String :=",
        '  "[" ++ String.intercalate "," (values.map renderInt64) ++ "]"',
    "private def renderIntegerList (values : List Int) : String :=",
    '  "[" ++ String.intercalate "," (values.map renderInteger) ++ "]"',
        "private def renderInt64Pair (value : Int64 × Int64) : String :=",
        '  "(" ++ renderInt64 value.1 ++ "," ++ renderInt64 value.2 ++ ")"',
        "",
        "set_option maxRecDepth 100000 in",
        "def main : IO Unit := do",
    ]
    for case in cases:
        expression = module + "." + case["function"] + " " + " ".join(
            _literal(value) for value in case["inputs"])
        rendered = LEAN_RENDERERS[case["result"]]
        lines.append(f"  IO.println ({_string(case['id'] + chr(9))} ++ {rendered} ({expression}))")
    return "\n".join(lines) + "\n"


def parse_runner_output(output: str, expected_ids: list[str], runner: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line_number, line in enumerate(output.splitlines(), 1):
        if not line:
            continue
        if "\t" not in line:
            raise PipelineError(runner, f"Malformed {runner} output on line {line_number}: {line}")
        case_id, value = line.split("\t", 1)
        if case_id in values:
            raise PipelineError(runner, f"Duplicate case id in {runner} output: {case_id}")
        values[case_id] = value
    expected = set(expected_ids)
    missing = expected - values.keys()
    unexpected = values.keys() - expected
    if missing or unexpected:
        details = []
        if missing:
            details.append("missing " + ", ".join(sorted(missing)))
        if unexpected:
            details.append("unexpected " + ", ".join(sorted(unexpected)))
        raise PipelineError(runner, f"Invalid {runner} case set: {'; '.join(details)}")
    return values


def _source_root(source: Path, module: str) -> Path:
    root = source.parent
    for _ in module.split(".")[:-1]:
        root = root.parent
    return root


def run_suite(config: dict, suite: dict, env: dict[str, str], deadline: float,
              target: dict[str, object], artifacts_dir: Path,
              oracle_package_db: Path | None) -> dict:
    module = suite["module"]
    source = (REPO / suite["source"]).resolve()
    if not source.is_file():
        raise PipelineError("configuration", f"Missing differential source: {source}")
    cases = expand_cases(config, suite)
    with tempfile.TemporaryDirectory(prefix="ghccore-differential-") as tmp:
        work = Path(tmp)
        modules = transpile(source, work, env, deadline, semantics="conservative",
                            audit=False, target=target)
        entries = [entry for entry in modules if entry["module"] == module]
        if len(entries) != 1:
            raise PipelineError("configuration", f"Source does not define configured module {module}")

        oracle_dir = work / "oracle"
        oracle_dir.mkdir()
        ghc_source = oracle_dir / "Main.hs"
        ghc_source.write_text(haskell_runner(module, cases))
        ghc_executable = oracle_dir / "oracle"
        oracle_env = env.copy()
        if oracle_package_db is not None:
            oracle_env["GHC_PACKAGE_PATH"] = str(oracle_package_db)
        require(run(["ghc-9.2.7", "-ignore-dot-ghci", "-fforce-recomp", "-v0",
                     "-odir", str(oracle_dir), "-hidir", str(oracle_dir),
                     "-i" + str(_source_root(source, module)), str(ghc_source),
                     "-o", str(ghc_executable)],
                    cwd=oracle_dir, env=oracle_env, deadline=deadline, phase="oracle-ghc"),
                "oracle-ghc")
        ghc_output = require(run([str(ghc_executable)], cwd=oracle_dir, env=env,
                                 deadline=deadline, phase="oracle-ghc"), "oracle-ghc")

        root, lean_env = private_lean_environment(work, env, deadline)
        for entry in modules:
            lean = Path(entry["lean"])
            require(run(["lean", "--root=" + str(root), "-o", str(lean.with_suffix(".olean")),
                         str(lean)], cwd=root, env=lean_env, deadline=deadline,
                        phase="oracle-lean"), "oracle-lean")
        lean_source = root / "DifferentialRunner.lean"
        lean_source.write_text(lean_runner(module, cases))
        lean_output = require(run(["lean", "--root=" + str(root), "--run", str(lean_source)],
                                  cwd=root, env=lean_env, deadline=deadline,
                                  phase="oracle-lean"), "oracle-lean")
        ensure_unchanged(modules)

        ids = [case["id"] for case in cases]
        ghc_values = parse_runner_output(ghc_output, ids, "oracle-ghc")
        lean_values = parse_runner_output(lean_output, ids, "oracle-lean")
        outcomes = []
        for case in cases:
            case_id = case["id"]
            matched = ghc_values[case_id] == lean_values[case_id]
            outcomes.append({**case, "ghc": ghc_values[case_id], "lean": lean_values[case_id],
                             "status": "matched" if matched else "mismatch"})
        matched_count = sum(case["status"] == "matched" for case in outcomes)
        outcome = {
            "module": module,
            "source": suite["source"],
            "sourceSha256": digest(source),
            "generatedSha256": digest(Path(entries[0]["lean"])),
            "status": "passed" if matched_count == len(outcomes) else "mismatch",
            "sampleCount": len(outcomes),
            "matchedCount": matched_count,
            "cases": outcomes,
        }
        if matched_count != len(outcomes):
            generated = artifacts_dir / (module.replace(".", "_") + ".lean")
            atomic_write(generated, Path(entries[0]["lean"]).read_text())
            outcome["generatedLeanPath"] = str(generated)
        return outcome


def differential(config_path: Path, timeout: float, artifacts_root: Path,
                 oracle_package_db: Path | None = None) -> dict:
    started = time.monotonic()
    deadline = started + timeout
    report = {
        "schemaVersion": 1,
        "runId": str(uuid.uuid4()),
        "claim": "sampled-differential",
        "translationCertified": False,
        "semantics": "conservative",
        "configuration": str(config_path),
        "accepted": False,
        "suites": [],
    }
    env = tool_env()
    try:
        config = load_config(config_path)
        if oracle_package_db is not None:
            if not oracle_package_db.is_dir():
                raise ValueError(f"Missing oracle package database: {oracle_package_db}")
            report["oraclePackageDb"] = str(oracle_package_db)
        report["configurationSha256"] = digest(config_path)
        report["seed"] = config["seed"]
        target = ghc_target(env, deadline)
        report["toolchain"] = {
            "lean": (REPO / "lean-toolchain").read_text().strip(),
            "ghc": "9.2.7",
            "target": target,
            "transpilerSha256": digest(REPO / ".lake/build/bin/ghccoretolean"),
            "runtimeSha256": digest(REPO / ".lake/build/lib/lean/GhcCoreToLean/Runtime.olean"),
        }
        for suite in config["suites"]:
            try:
                outcome = run_suite(config, suite, env, deadline, target,
                                    artifacts_root / report["runId"], oracle_package_db)
            except PipelineError as exc:
                outcome = {"module": suite["module"], "source": suite["source"],
                           "status": exc.status, "phase": exc.phase, "detail": str(exc),
                           "sampleCount": 0, "matchedCount": 0, "cases": []}
            report["suites"].append(outcome)
        report["sampleCount"] = sum(suite["sampleCount"] for suite in report["suites"])
        report["matchedCount"] = sum(suite["matchedCount"] for suite in report["suites"])
        report["status"] = ("passed" if report["suites"]
                            and all(suite["status"] == "passed" for suite in report["suites"])
                            else "failed")
        report["accepted"] = report["status"] == "passed"
        report["phase"] = "complete"
    except PipelineError as exc:
        report.update(status=exc.status, phase=exc.phase, detail=str(exc), accepted=False)
    except KeyboardInterrupt:
        report.update(status="cancelled", phase="cancelled", accepted=False)
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        report.update(status="error", phase="configuration", detail=str(exc), accepted=False)
    report["elapsedSeconds"] = round(time.monotonic() - started, 3)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=REPO / "tests/differential.json")
    parser.add_argument("--report", type=Path, default=REPO / ".lake/differential-results.json")
    parser.add_argument("--json", action="store_true", help="emit one JSON result to stdout")
    parser.add_argument("--timeout", type=float, default=900,
                        help="whole-run wall-clock limit in seconds")
    parser.add_argument("--oracle-package-db", type=Path,
                        help="temporary GHC package database for the direct oracle build only")
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--timeout must be finite and positive")
    cancel_on_termination()
    config_path = args.config.resolve()
    artifacts_root = args.report.resolve().parent / "differential-artifacts"
    report = differential(config_path, args.timeout, artifacts_root,
                          args.oracle_package_db.resolve() if args.oracle_package_db else None)
    atomic_write(args.report.resolve(), json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    if args.json:
        print(json.dumps(report, ensure_ascii=False))
    else:
        for suite in report["suites"]:
            print(f"{suite['status'].upper()} {suite['module']}: "
                  f"{suite['matchedCount']}/{suite['sampleCount']} samples matched")
            if suite.get("detail"):
                print("  " + suite["detail"])
            for case in suite["cases"]:
                if case["status"] == "mismatch":
                    print(f"  {case['id']}: GHC={case['ghc']} Lean={case['lean']}")
        print(f"{report['status']}: {report.get('matchedCount', 0)}/"
              f"{report.get('sampleCount', 0)} sampled executions matched; report: {args.report}")
        print("This is differential test evidence; translation correctness is not certified.")
        if report.get("detail"):
            print(report["detail"])
    return 0 if report["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
