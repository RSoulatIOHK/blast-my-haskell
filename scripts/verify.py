#!/usr/bin/env python3
"""Verify a private Lean model and report completed, auditable results."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
import tempfile
import time
import uuid

from pipeline import (REPO, PipelineError, ensure_unchanged, require, run,
                      cancel_on_termination, digest, ghc_target,
                      private_lean_environment, tool_env, transpile)

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SMT_AXIOM = "Blaster.Tactic.blasterProven"
AUDIT_PREFIX = "GHCCORE_AUDIT:"


def proof_status(axioms: list[str]) -> str:
    remaining = set(axioms) - STANDARD_AXIOMS
    if "sorryAx" in remaining:
        return "admitted"
    if remaining - {SMT_AXIOM}:
        return "assumed"
    return "smt_valid" if SMT_AXIOM in remaining else "proved"


def parse_diagnostics(stdout: str) -> tuple[list[dict], list[list[dict]]]:
    diagnostics, audits = [], []
    for line in stdout.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue  # #eval and other commands may print non-diagnostic text.
        if not isinstance(msg, dict) or "severity" not in msg:
            continue
        diagnostics.append(msg)
        data = msg.get("data", "")
        if msg["severity"] == "information" and isinstance(data, str) and data.startswith(AUDIT_PREFIX):
            audits.append(json.loads(data[len(AUDIT_PREFIX):]))
    return diagnostics, audits


def module_result(module: dict, stdout: str, stderr: str, returncode: int) -> dict:
    diagnostics, audits = parse_diagnostics(stdout)
    errors = [d for d in diagnostics if d["severity"] == "error"]
    result = {"module": module["module"], "source": module["source"],
              "sha256": module["sha256"], "properties": [],
              "diagnostics": diagnostics, "warnings": module["warnings"],
              "stderr": stderr}
    if returncode or errors:
        # A solver counterexample is a counterexample to the MODEL. Ordinary
        # elaboration errors and unsuccessful proof search are not refutations.
        result["status"] = ("refuted" if any("Goal was falsified" in d.get("data", "")
                                            for d in errors) else "error")
        return result
    if len(audits) != 1:
        result.update(status="error", detail="Expected exactly one completed theorem audit")
        return result
    entries = audits[0]
    for block in module["map"]["blocks"]:
        theorems = sorted((e for e in entries if block["lean"][0] <= e["line"] <= block["lean"][1]),
                          key=lambda e: e["name"])
        for theorem in theorems:
            theorem["status"] = proof_status(theorem["axioms"])
        # A block of definitions/#eval is not evidence of a verified property.
        status = aggregate([t["status"] for t in theorems]) if theorems else "no_theorem"
        result["properties"].append({"hs": block["hs"], "status": status, "theorems": theorems})
    result["status"] = aggregate([p["status"] for p in result["properties"]])
    return result


def aggregate(statuses: list[str]) -> str:
    if not statuses:
        return "no_properties"
    for status in ("error", "refuted", "admitted", "assumed", "no_theorem", "smt_valid"):
        if status in statuses:
            return status
    return "proved"


def accepted(status: str, trust_smt: bool) -> bool:
    return status == "proved" or (status == "smt_valid" and trust_smt)


def verify(source: Path, *, semantics: str, trust_smt: bool, timeout: float) -> dict:
    started = time.monotonic()
    deadline = started + timeout
    report = {"schemaVersion": 1, "runId": str(uuid.uuid4()), "source": str(source),
              "semantics": semantics, "trustSmt": trust_smt, "claim": "lean-model",
              "translationCertified": False, "modules": [], "accepted": False}
    env = tool_env()
    try:
        manifest = json.loads((REPO / "lake-manifest.json").read_text())
        target = ghc_target(env, deadline)
        report["toolchain"] = {
            "lean": (REPO / "lean-toolchain").read_text().strip(),
            "ghc": "9.2.7",
            "target": target,
            "dependencies": [{"name": p["name"], "revision": p.get("rev")}
                             for p in manifest["packages"]],
            "transpilerSha256": digest(REPO / ".lake/build/bin/ghccoretolean"),
            "runtimeSha256": digest(REPO / ".lake/build/lib/lean/GhcCoreToLean/Runtime.olean"),
            "auditSha256": digest(REPO / ".lake/build/lib/lean/GhcCoreToLean/Audit.olean"),
        }
        blaster_state = run(["git", "status", "--porcelain"], cwd=REPO / ".lake/packages/Blaster",
                            env=env, deadline=deadline, phase="setup")
        report["toolchain"]["blasterDirty"] = bool(require(blaster_state, "setup").strip())
        with tempfile.TemporaryDirectory(prefix="ghccore-verify-") as tmp:
            work = Path(tmp)
            modules = transpile(source, work, env, deadline, semantics=semantics, audit=True,
                                target=target)
            root, lean_env = private_lean_environment(work, env, deadline)
            support = REPO / ".lake/build/lib/lean/GhcCoreToLean"
            for module in modules:
                lean = Path(module["lean"])
                completed = run(["lean", "--json", "--root=" + str(root),
                                 "-o", str(lean.with_suffix(".olean")), str(lean)],
                                cwd=root, env=lean_env, deadline=deadline, phase="lean")
                outcome = module_result(module, completed.stdout, completed.stderr, completed.returncode)
                outcome["generatedSha256"] = digest(lean)
                outcome["sourceMap"] = module["map"]
                report["modules"].append(outcome)
                if outcome["status"] in ("error", "refuted"):
                    report.update(status=outcome["status"], phase="lean")
                    break
            else:
                statuses = [m["status"] for m in report["modules"]
                            if m["status"] != "no_properties"]
                # Dependencies may be unannotated. The requested entry may not.
                if report["modules"][-1]["status"] == "no_properties":
                    report["status"] = "no_properties"
                else:
                    report["status"] = aggregate(statuses)
                report["phase"] = "complete"
            ensure_unchanged(modules)
            for field, artifact in [
                ("transpilerSha256", REPO / ".lake/build/bin/ghccoretolean"),
                ("runtimeSha256", support / "Runtime.olean"),
                ("auditSha256", support / "Audit.olean"),
            ]:
                if digest(artifact) != report["toolchain"][field]:
                    raise PipelineError("snapshot", "Verification tools changed during the run",
                                        status="stale")
            report["accepted"] = accepted(report["status"], trust_smt)
    except PipelineError as exc:
        report.update(status=exc.status, phase=exc.phase, detail=str(exc), accepted=False)
    except KeyboardInterrupt:
        report.update(status="cancelled", phase="cancelled", accepted=False)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        report.update(status="error", phase="protocol", detail=str(exc), accepted=False)
    report["elapsedSeconds"] = round(time.monotonic() - started, 3)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--json", action="store_true", help="emit one JSON result to stdout")
    parser.add_argument("--semantics", choices=["conservative", "approximate"], default="conservative",
                        help="conservative rejects known approximations; neither policy certifies translation")
    parser.add_argument("--trust-smt", action="store_true", help="accept SMT results without proof reconstruction")
    parser.add_argument("--timeout", type=float, default=600, help="whole-run wall-clock limit in seconds")
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--timeout must be finite and positive")
    cancel_on_termination()
    report = verify(args.source.resolve(), semantics=args.semantics,
                    trust_smt=args.trust_smt, timeout=args.timeout)
    if args.json:
        print(json.dumps(report, ensure_ascii=False))
    else:
        print(f"{report['status']}: Lean model ({report['semantics']} semantics); accepted={report['accepted']}")
        print("Translation correctness is not certified. SMT results require explicit trust.")
        if report.get("detail"):
            print(report["detail"])
        for module in report["modules"]:
            print(f"  {module['module']}: {module['status']}")
            for prop in module["properties"]:
                print(f"    lines {prop['hs'][0]}–{prop['hs'][1]}: {prop['status']}")
                for theorem in prop["theorems"]:
                    print(f"      {theorem['name']}: {', '.join(theorem['axioms']) or 'no axioms'}")
            for diagnostic in module["diagnostics"]:
                if diagnostic["severity"] == "error":
                    print(diagnostic.get("data", ""))
    return 0 if report["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
