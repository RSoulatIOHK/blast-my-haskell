#!/usr/bin/env python3
"""Translate selected Core from the pinned data-ordlist Cabal package."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tempfile
import time

from differential import expand_cases, load_config, parse_runner_output
from ordlist_package_fidelity import (ARCHIVE_SHA256, MODULE_SHA256,
                                      execute_oracle, extract_pinned_package,
                                      sha256)
from pipeline import (REPO, PipelineError, atomic_write, ghc_target,
                      private_lean_environment, require, require_supported_target,
                      run, tool_env)


ROOTS = ("unionBy", "mergeBy")
MODULE = "Data.List.Ordered"
ORIGINAL_DEPENDENCIES = "Build-Depends:     base >= 2 && < 5"
INSTRUMENTED_DEPENDENCIES = (
    "Build-Depends:     base >= 2 && < 5, ghc-dump-core, "
    "decl-plugin, lean-spec, spec-plugin\n"
    "  ghc-options: -fplugin GhcDump.Plugin -fplugin GhcDeclDump -fplugin GhcSpecDump"
)


def instrument_package(package: Path) -> tuple[str, str]:
    cabal = package / "data-ordlist.cabal"
    original = cabal.read_bytes()
    source = original.decode()
    if source.count(ORIGINAL_DEPENDENCIES) != 1:
        raise ValueError("Pinned Cabal dependencies changed; review instrumentation")
    cabal.write_text(source.replace(ORIGINAL_DEPENDENCIES, INSTRUMENTED_DEPENDENCIES, 1))
    plugin_packages = ("decl-plugin", "lean-spec", "spec-plugin")
    (package / "cabal.project").write_text(
        "with-compiler: ghc-9.2.7\npackages:\n  .\n" +
        "".join(f'  "{REPO / "shim" / name}"\n' for name in plugin_packages))
    (package / "cabal.project.freeze").write_bytes(
        (REPO / "shim/cabal.project.freeze").read_bytes())
    return sha256(original), sha256(cabal.read_bytes())


def list_literal(values: list[int]) -> str:
    return "[" + ", ".join(f"({v})" if v < 0 else str(v) for v in values) + "]"


def lean_runner(cases: list[dict]) -> str:
    lines = [
        "import GhcCoreToLean.Generated.Data.List.Ordered",
        "private def renderInt64 (value : Int64) : String := toString value.toInt",
        "private def renderList (values : List Int64) : String :=",
        '  "[" ++ String.intercalate "," (values.map renderInt64) ++ "]"',
        "set_option maxRecDepth 100000 in",
        "def main : IO Unit := do",
    ]
    for case in cases:
        function = {"unionInt": "unionBy", "mergeInt": "mergeBy"}[case["function"]]
        left, right = case["inputs"]
        expression = (f"Data.List.Ordered.{function} compare "
                      f"{list_literal(left)} {list_literal(right)}")
        label = json.dumps(case["id"] + "\t")
        lines.append(f"  IO.println ({label} ++ renderList ({expression}))")
    return "\n".join(lines) + "\n"


def check(config_path: Path, report_path: Path, timeout: float) -> int:
    config = load_config(config_path)
    suites = [s for s in config["suites"] if s["module"] == "OrderedPilot"]
    if len(suites) != 1:
        raise ValueError("Expected exactly one OrderedPilot differential suite")
    cases = [case for case in expand_cases(config, suites[0])
             if case["function"] in ("unionInt", "mergeInt")]
    if not cases:
        raise ValueError("No merge or union cases configured")

    env = tool_env()
    env.pop("GHC_PACKAGE_PATH", None)
    deadline = time.monotonic() + timeout
    target = ghc_target(env, deadline)
    require_supported_target(target, "conservative")
    with tempfile.TemporaryDirectory(prefix="ordlist-core-import-") as temp:
        work = Path(temp)
        package = extract_pinned_package(work)
        original_cabal_sha, instrumented_cabal_sha = instrument_package(package)
        decls = work / "decls"
        specs = work / "specs"
        decls.mkdir()
        specs.mkdir()
        build_env = {**env, "GHC_DECL_DUMP_DIR": str(decls), "LEAN_SPEC_DIR": str(specs)}
        require(run(["cabal", "build", "data-ordlist", "--offline"], cwd=package,
                    env=build_env, deadline=deadline, phase="package-core"), "package-core")

        dumps = list((package / "dist-newstyle").rglob("Data/List/Ordered.pass-0000.cbor"))
        sidecar = decls / "Data.List.Ordered.decls.json"
        if len(dumps) != 1 or not sidecar.is_file():
            raise PipelineError("package-core", "Expected one package Core dump and declaration sidecar")
        shim = require(run(["cabal", "list-bin", "exe:ghc-core-shim"],
                           cwd=REPO / "shim", env=env, deadline=deadline,
                           phase="setup"), "setup").strip()
        core = work / "Ordered.json"
        core.write_text(require(run([shim, str(dumps[0]), "--decls", str(sidecar)],
                                    cwd=work, env=env, deadline=deadline,
                                    phase="core-shim"), "core-shim"))
        lean = work / "lean/GhcCoreToLean/Generated/Data/List/Ordered.lean"
        lean.parent.mkdir(parents=True)
        translate_env = {**env, "GHCCORE_ROOTS": ",".join(ROOTS),
                         "GHCCORE_SEMANTICS": "conservative",
                         "GHCCORE_INT_BITS": str(target["intBits"])}
        compiler = REPO / ".lake/build/bin/ghccoretolean"
        result = run([str(compiler), str(core), str(lean), MODULE], cwd=work,
                     env=translate_env, deadline=deadline, phase="translate")
        require(result, "translate")
        if result.stderr.strip():
            raise PipelineError("translate", "Conservative import emitted warnings:\n" + result.stderr)
        lean_text = lean.read_text()
        if re.search(r"\b(sorry|sorryAx|admit)\b", lean_text):
            raise PipelineError("translate", "Imported Lean model contains an admission")

        lean_root, lean_env = private_lean_environment(work, env, deadline)
        require(run(["lean", "--root=" + str(lean_root), "-o",
                     str(lean.with_suffix(".olean")), str(lean)],
                    cwd=lean_root, env=lean_env, deadline=deadline,
                    phase="lean-build"), "lean-build")
        runner = lean_root / "PackageCoreRunner.lean"
        runner.write_text(lean_runner(cases))
        lean_output = require(run(["lean", "--root=" + str(lean_root), "--run", str(runner)],
                                  cwd=lean_root, env=lean_env, deadline=deadline,
                                  phase="lean-run"), "lean-run")
        lean_values = parse_runner_output(lean_output, [c["id"] for c in cases], "lean")
        proofs = lean_root / "PackageProofs.lean"
        proof_source = (REPO / "tests/pilot/data-ordlist/PackageProofs.lean").read_text()
        for function, pinned in (("mergeBy", "4577"), ("unionBy", "4841")):
            match = re.search(r"^def " + function + r"\b[^\n]*\n\s*\(let rec (loop_\d+)",
                              lean_text, re.MULTILINE)
            if match is None:
                raise PipelineError("package-proofs", f"Missing generated loop for {function}")
            marker = function + ".loop_" + pinned
            if proof_source.count(marker) != 1:
                raise PipelineError("package-proofs", f"Expected one proof reference to {marker}")
            proof_source = proof_source.replace(marker, function + "." + match.group(1))
        proofs.write_text(proof_source)
        proof_output = require(run(["lean", "--root=" + str(lean_root), str(proofs)],
                                   cwd=lean_root, env=lean_env, deadline=deadline,
                                   phase="package-proofs"), "package-proofs")
        audits = re.findall(r"GHCCORE_AUDIT:(\[[^\n]*\])", proof_output)
        if len(audits) != 1:
            raise PipelineError("package-proofs", "Expected one theorem axiom audit")
        theorems = json.loads(audits[0])
        axiom_sets = {entry["name"].split(".")[-1]: set(entry["axioms"])
                      for entry in theorems}
        expected = {"package_merge_length", "package_union_membership"}
        allowed = {"propext", "Classical.choice", "Quot.sound",
                   "Blaster.Tactic.blasterProven"}
        if (set(axiom_sets) != expected or len(theorems) != len(expected)
                or any(axioms - allowed for axioms in axiom_sets.values())
                or "Blaster.Tactic.blasterProven" not in axiom_sets["package_merge_length"]
                or "Blaster.Tactic.blasterProven" in axiom_sets["package_union_membership"]):
            raise PipelineError("package-proofs", "Unexpected package theorem axiom set")
        ghc_values = execute_oracle("PackageSubject", cases, work / "package-oracle",
                                    package, env, deadline)
        core_sha = sha256(core.read_bytes())
        lean_sha = sha256(lean.read_bytes())

    mismatches = [{"id": case["id"], "ghc": ghc_values[case["id"]],
                   "lean": lean_values[case["id"]]}
                  for case in cases if ghc_values[case["id"]] != lean_values[case["id"]]]
    report = {"package": "data-ordlist", "version": "0.4.7.0",
              "module": MODULE, "roots": list(ROOTS),
              "archiveSha256": ARCHIVE_SHA256, "moduleSha256": MODULE_SHA256,
              "originalCabalSha256": original_cabal_sha,
              "instrumentedCabalSha256": instrumented_cabal_sha,
              "coreSha256": core_sha, "leanSha256": lean_sha,
              "theoremAxioms": {name: sorted(axioms) for name, axioms in axiom_sets.items()},
              "translationCertified": False,
              "cases": len(cases), "matched": len(cases) - len(mismatches),
              "mismatches": mismatches}
    atomic_write(report_path, json.dumps(report, indent=2) + "\n")
    if mismatches:
        print(f"Package Core import failed: {len(mismatches)}/{len(cases)} mismatches",
              file=sys.stderr)
        return 1
    print(f"Package Core import passed: {len(cases)}/{len(cases)} GHC/Lean executions matched")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=REPO / "tests/differential.json")
    parser.add_argument("--report", type=Path, default=REPO / ".lake/ordlist-core-import.json")
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    try:
        return check(args.config, args.report, args.timeout)
    except (OSError, ValueError, PipelineError) as exc:
        print(f"Package Core import error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
