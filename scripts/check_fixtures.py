#!/usr/bin/env python3
"""Run explicitly classified end-to-end fixtures, including expected failures."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import subprocess
import sys

from pipeline import REPO, atomic_write
from verify import verify


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", default="", help="substring of fixture id")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--report", type=Path, default=REPO / ".lake/verification-results.json")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    fixtures = json.loads((REPO / "tests/fixtures.json").read_text())
    ids = [f["id"] for f in fixtures]
    if len(ids) != len(set(ids)):
        parser.error("Duplicate fixture ids")
    exclusions = json.loads((REPO / "tests/fixture-exclusions.json").read_text())
    excluded = [item["source"] for item in exclusions]
    if len(excluded) != len(set(excluded)) or set(excluded) & {f["source"] for f in fixtures}:
        parser.error("Duplicate or conflicting fixture exclusions")
    if any(not source.startswith("examples/haskell/") or not source.endswith(".hs")
           for source in excluded):
        parser.error("Fixture exclusions must name Haskell examples")
    if any(not isinstance(item.get("reason"), str) or not item["reason"].strip()
           for item in exclusions):
        parser.error("Every fixture exclusion needs a reason")
    available = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "examples/haskell"],
        cwd=REPO, text=True)
    sources = {p for p in available.splitlines() if p.endswith(".hs")}
    missing = sources - {f["source"] for f in fixtures} - set(excluded)
    if missing:
        parser.error("Unclassified Haskell examples: " + ", ".join(sorted(missing)))
    selected = [f for f in fixtures if args.only in f["id"]]
    if not selected:
        parser.error("No fixtures selected")
    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {pool.submit(verify, REPO / f["source"], semantics=f.get("semantics", "approximate"),
                               trust_smt=f.get("trustSmt", True), timeout=f.get("timeout", 180)): f
                   for f in selected}
        for future in as_completed(pending):
            fixture = pending[future]
            report = future.result()
            ok = report["status"] == fixture["expected"]
            if "phase" in fixture:
                ok = ok and report["phase"] == fixture["phase"]
            if "accepted" in fixture:
                ok = ok and report["accepted"] == fixture["accepted"]
            if "contains" in fixture:
                ok = ok and fixture["contains"] in json.dumps(report, ensure_ascii=False)
            if "minTheorems" in fixture:
                count = sum(len(p["theorems"]) for m in report["modules"] for p in m["properties"])
                ok = ok and count >= fixture["minTheorems"]
            results.append({"id": fixture["id"], "passed": ok, "expected": fixture["expected"], "result": report})
            print(f"{'PASS' if ok else 'FAIL'} {fixture['id']}: {report['status']} "
                  f"(expected {fixture['expected']}, {report['elapsedSeconds']}s)", flush=True)
    results.sort(key=lambda r: r["id"])
    atomic_write(args.report.resolve(), json.dumps(results, ensure_ascii=False, indent=2) + "\n")
    failures = sum(not r["passed"] for r in results)
    print(f"{len(results) - failures}/{len(results)} fixtures passed; report: {args.report}")
    return int(failures != 0)


if __name__ == "__main__":
    sys.exit(main())
