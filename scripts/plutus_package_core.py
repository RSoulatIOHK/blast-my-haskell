#!/usr/bin/env python3
"""Prove and compare selected Core from a pinned plutus-tx Cabal build."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time

from differential import expand_cases, haskell_runner, load_config, parse_runner_output
from pipeline import (REPO, PipelineError, atomic_write, parse_ghc_target,
                      private_lean_environment, require, require_supported_target,
                      run, tool_env)


COMMIT = "2f8edc6f01ebd6683c8494afeef026d1cab54713"
SOURCE_SHA256 = "91d0590e3ee1a47829a689600bf83a2cf22a561a142e74810062549c71095937"
REMOTE = "https://github.com/IntersectMBO/plutus.git"
MODULE = "PlutusTx.List"
ROOTS = ("revAppend", "reverse")
PILOT = REPO / "tests/pilot/plutus-tx"
DUMPER = REPO / "shim/ghc96/ghc-dump-core"
COMPILER = "ghc-9.6.6"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args: list[str], cwd: Path, env: dict[str, str], deadline: float,
            phase: str) -> str:
    return require(run(args, cwd=cwd, env=env, deadline=deadline, phase=phase), phase)


def pinned_source(work: Path, source: Path | None, env: dict[str, str],
                  deadline: float) -> Path:
    upstream = work / "upstream"
    if source is None:
        upstream.mkdir()
        command(["git", "init", "-q"], upstream, env, deadline, "source")
        command(["git", "remote", "add", "origin", REMOTE], upstream, env, deadline, "source")
        command(["git", "sparse-checkout", "init", "--cone"], upstream, env, deadline, "source")
        command(["git", "sparse-checkout", "set", "plutus-core", "plutus-tx"],
                upstream, env, deadline, "source")
        command(["git", "fetch", "--depth", "1", "origin", COMMIT],
                upstream, env, deadline, "source")
        command(["git", "checkout", "--detach", "-q", "FETCH_HEAD"],
                upstream, env, deadline, "source")
    else:
        resolved = source.resolve()
        head = command(["git", "rev-parse", "HEAD"], resolved, env, deadline, "source").strip()
        if head != COMMIT:
            raise PipelineError("source", f"Source checkout is {head}, expected {COMMIT}")
        for name in ("plutus-core", "plutus-tx"):
            shutil.copytree(resolved / name, upstream / name,
                            ignore=shutil.ignore_patterns("dist-newstyle", "*.pass-*.cbor"))
        shutil.copy2(resolved / "cabal.project", upstream / "cabal.project")
    module = upstream / "plutus-tx/src/PlutusTx/List.hs"
    if sha256(module) != SOURCE_SHA256:
        raise PipelineError("source", "Pinned PlutusTx.List source hash changed")
    return upstream


def instrument(upstream: Path) -> tuple[str, str]:
    cabal = upstream / "plutus-tx/plutus-tx.cabal"
    original = cabal.read_text()
    dependency = "    , formatting\n    , hashable\n"
    options = ("  default-extensions: Strict\n\n"
               "  -- See Note [-fno-full-laziness in Plutus Tx]\n  ghc-options:\n")
    if original.count(dependency) != 1 or original.count(options) != 1:
        raise PipelineError("instrument", "Pinned plutus-tx Cabal layout changed")
    modified = original.replace(dependency,
                                "    , formatting\n    , ghc-dump-core\n    , hashable\n", 1)
    modified = modified.replace(options, options + "    -fplugin=GhcDump.Plugin\n", 1)
    cabal.write_text(modified)
    return hashlib.sha256(original.encode()).hexdigest(), sha256(cabal)


def project_file(work: Path, upstream: Path) -> Path:
    original = (upstream / "cabal.project").read_text()
    marker = "\npackages:"
    if original.count(marker) != 1:
        raise PipelineError("project", "Pinned Plutus project layout changed")
    header = original.split(marker, 1)[0]
    paths = [upstream / "plutus-core", upstream / "plutus-tx", DUMPER, REPO / "shim"]
    project = work / "cabal.project"
    project.write_text(header + "\nwith-compiler: " + COMPILER + "\npackages:\n"
                       + "".join(f'  "{path}"\n' for path in paths)
                       + "\ntests: False\nbenchmarks: False\n"
                       + "package plutus-core\n  flags: -with-inline-r -with-cert -with-crypto\n"
                       + "constraints: text == 2.0.2\n")
    return project


def list_literal(values: list[int]) -> str:
    return "[" + ", ".join(f"({v})" if v < 0 else str(v) for v in values) + "]"


def lean_runner(cases: list[dict]) -> str:
    lines = [
        "import GhcCoreToLean.Generated.PlutusTx.List",
        "private def renderInt64 (value : Int64) : String := toString value.toInt",
        "private def renderList (values : List Int64) : String :=",
        '  "[" ++ String.intercalate "," (values.map renderInt64) ++ "]"',
        "set_option maxRecDepth 100000 in",
        "def main : IO Unit := do",
    ]
    for case in cases:
        args = " ".join(list_literal(values) for values in case["inputs"])
        function = {"revAppendInt": "revAppend", "reverseInt": "reverse"}[case["function"]]
        label = json.dumps(case["id"] + "\t")
        lines.append(f"  IO.println ({label} ++ renderList (PlutusTx.List.{function} {args}))")
    return "\n".join(lines) + "\n"


def proof_axioms(output: str) -> dict[str, list[str]]:
    audits = re.findall(r"GHCCORE_AUDIT:(\[[^\n]*\])", output)
    if len(audits) != 1:
        raise PipelineError("package-proofs", "Expected one theorem axiom audit")
    entries = json.loads(audits[0])
    axioms = {entry["name"].split(".")[-1]: set(entry["axioms"]) for entry in entries}
    expected = {"package_rev_append_spec", "package_reverse_model",
                "package_reverse_involutive", "package_reverse_length",
                "package_rev_append_length"}
    if set(axioms) != expected or len(entries) != len(expected):
        raise PipelineError("package-proofs", "Unexpected package theorem set")
    for name in expected - {"package_rev_append_length"}:
        if axioms[name] != {"propext"}:
            raise PipelineError("package-proofs", f"Unexpected axioms in {name}: {axioms[name]}")
    blaster = "Blaster.Tactic.blasterProven"
    length_axioms = axioms["package_rev_append_length"]
    if blaster not in length_axioms or length_axioms - {"propext", blaster}:
        raise PipelineError("package-proofs", f"Unexpected axioms in length law: {length_axioms}")
    return {name: sorted(values) for name, values in axioms.items()}


def check(work: Path, source: Path | None, package_db: Path | None,
          update_index: bool,
          env: dict[str, str], deadline: float) -> dict:
    version = command([COMPILER, "--numeric-version"], REPO, env, deadline, "setup").strip()
    if version != "9.6.6":
        raise PipelineError("setup", f"Expected GHC 9.6.6, got {version}")
    target = parse_ghc_target(command([COMPILER, "--info"], REPO, env, deadline, "setup"))
    require_supported_target(target, "conservative")
    upstream = pinned_source(work, source, env, deadline)
    original_cabal, instrumented_cabal = instrument(upstream)
    project = project_file(work, upstream)
    cabal_args = ["--project-file=" + str(project), "--with-compiler=" + COMPILER]
    if package_db is not None:
        cabal_args.append("--package-db=" + str(package_db.resolve()))
    if update_index:
        command(["cabal", "update", "--project-file=" + str(project)],
                work, env, deadline, "package-index")
    command(["cabal", "build", *cabal_args, "plutus-tx:lib:plutus-tx",
             "ghc-core-shim:exe:ghc-core-shim", "-j2"], work, env, deadline, "package-build")
    dumps = list((work / "dist-newstyle").rglob("PlutusTx/List.pass-0000.cbor"))
    if len(dumps) != 1:
        raise PipelineError("package-core", f"Expected one package Core dump, got {len(dumps)}")
    shim = command(["cabal", "list-bin", *cabal_args, "ghc-core-shim:exe:ghc-core-shim"],
                   work, env, deadline, "setup").strip()
    core = work / "PlutusTx.List.json"
    core.write_text(command([shim, str(dumps[0])], work, env, deadline, "core-shim"))
    lean_root, lean_env = private_lean_environment(work, env, deadline)
    lean = lean_root / "GhcCoreToLean/Generated/PlutusTx/List.lean"
    lean.parent.mkdir(parents=True)
    translate_env = {**env, "GHCCORE_ROOTS": ",".join(ROOTS),
                     "GHCCORE_SEMANTICS": "conservative",
                     "GHCCORE_INT_BITS": str(target["intBits"])}
    result = run([str(REPO / ".lake/build/bin/ghccoretolean"), str(core), str(lean), MODULE],
                 cwd=work, env=translate_env, deadline=deadline, phase="translate")
    require(result, "translate")
    if result.stderr.strip():
        raise PipelineError("translate", "Conservative translation warnings:\n" + result.stderr)
    if re.search(r"\b(sorry|sorryAx|admit)\b", lean.read_text()):
        raise PipelineError("translate", "Package model contains an admission")
    command(["lean", "--root=" + str(lean_root), "-o", str(lean.with_suffix(".olean")),
             str(lean)], lean_root, lean_env, deadline, "lean-build")
    proof = lean_root / "PackageProofs.lean"
    proof.write_bytes((PILOT / "PackageProofs.lean").read_bytes())
    audit = proof_axioms(command(["lean", "--root=" + str(lean_root), str(proof)],
                                 lean_root, lean_env, deadline, "package-proofs"))
    config = load_config(REPO / "tests/differential.json")
    suites = [suite for suite in config["suites"] if suite["module"] == "PlutusListPilot"]
    if len(suites) != 1:
        raise PipelineError("cases", "Expected one PlutusListPilot differential suite")
    cases = expand_cases(config, suites[0])
    oracle_dir = work / "oracle"
    oracle_dir.mkdir()
    (oracle_dir / "PackageSubject.hs").write_text(
        "module PackageSubject where\n"
        "import qualified PlutusTx.List as P\n"
        "reverseInt :: [Int] -> [Int]\nreverseInt = P.reverse\n"
        "revAppendInt :: [Int] -> [Int] -> [Int]\nrevAppendInt = P.revAppend\n")
    oracle = oracle_dir / "oracle"
    (oracle_dir / "Main.hs").write_text(haskell_runner("PackageSubject", cases))
    command(["cabal", "exec", *cabal_args, "--", COMPILER, "-ignore-dot-ghci",
             "-fforce-recomp", "-v0", "-package", "plutus-tx",
             "-i" + str(oracle_dir), "-odir", str(oracle_dir), "-hidir", str(oracle_dir),
             str(oracle_dir / "Main.hs"), "-o", str(oracle)],
            work, env, deadline, "oracle-build")
    ghc_values = parse_runner_output(
        command([str(oracle)], work, env, deadline, "oracle-run"),
        [case["id"] for case in cases], "package-oracle")
    runner = lean_root / "PackageRunner.lean"
    runner.write_text(lean_runner(cases))
    lean_values = parse_runner_output(
        command(["lean", "--root=" + str(lean_root), "--run", str(runner)],
                lean_root, lean_env, deadline, "lean-run"),
        [case["id"] for case in cases], "package-lean")
    mismatches = [{"id": case["id"], "ghc": ghc_values[case["id"]],
                   "lean": lean_values[case["id"]]}
                  for case in cases if ghc_values[case["id"]] != lean_values[case["id"]]]
    return {"status": "passed" if not mismatches else "failed",
            "package": "plutus-tx", "module": MODULE, "roots": list(ROOTS),
            "upstreamCommit": COMMIT, "sourceSha256": SOURCE_SHA256,
            "originalCabalSha256": original_cabal,
            "instrumentedCabalSha256": instrumented_cabal,
            "dumpSha256": sha256(dumps[0]), "coreSha256": sha256(core),
            "leanSha256": sha256(lean), "theoremAxioms": audit,
            "sampleCount": len(cases), "matchedCount": len(cases) - len(mismatches),
            "mismatches": mismatches, "translationCertified": False,
            "trustSmt": True, "ghcVersion": version, "target": target}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="Local checkout at the pinned commit")
    parser.add_argument("--package-db", type=Path, help="Alternate GHC package DB")
    parser.add_argument("--update-index", action="store_true",
                        help="Update Hackage and CHaP package indexes before building")
    parser.add_argument("--report", type=Path, default=REPO / ".lake/plutus-package-core.json")
    parser.add_argument("--timeout", type=float, default=3600)
    parser.add_argument("--work-dir", type=Path, help="Retain build artifacts here")
    args = parser.parse_args()
    env = tool_env()
    env.pop("GHC_PACKAGE_PATH", None)
    deadline = time.monotonic() + args.timeout
    try:
        if args.work_dir is None:
            with tempfile.TemporaryDirectory(prefix="plutus-package-core-") as temp:
                report = check(Path(temp), args.source, args.package_db,
                               args.update_index, env, deadline)
        else:
            args.work_dir.mkdir(parents=True, exist_ok=False)
            report = check(args.work_dir.resolve(), args.source, args.package_db,
                           args.update_index, env, deadline)
    except (PipelineError, OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        report = {"status": "error", "phase": getattr(exc, "phase", "setup"),
                  "error": str(exc), "translationCertified": False}
    atomic_write(args.report, json.dumps(report, indent=2) + "\n")
    if report["status"] != "passed":
        print(f"Plutus package Core gate {report['status']}: {report.get('error', report.get('mismatches'))}",
              file=sys.stderr)
        return 1
    print(f"Plutus package Core gate passed: {report['matchedCount']}/{report['sampleCount']} cases; "
          f"report: {args.report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
