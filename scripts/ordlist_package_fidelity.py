#!/usr/bin/env python3
"""Compare the ordered-list pilot with the pinned, built Cabal package."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile
import tempfile
import time

from differential import expand_cases, haskell_runner, load_config, parse_runner_output
from pipeline import REPO, PipelineError, atomic_write, require, run, tool_env


ARCHIVE = REPO / "tests/pilot/data-ordlist/vendor/data-ordlist-0.4.7.0.tar.gz"
ARCHIVE_SHA256 = "6f6c1e7a9a9155ad78ca78cb9abd6f7e2e1c78b3e549b179dc0874e6428f490d"
MODULE_SHA256 = "73c11909892d3ce36dcab3688f5429b4db20ed752137a5d130f7ce3f00870aee"
PACKAGE_DIR = "data-ordlist-0.4.7.0"
FUNCTIONS = ("isSortedBy", "memberBy", "insertSetBy", "unionBy", "mergeBy")
PILOT = REPO / "tests/pilot/data-ordlist/OrderedPilot.hs"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def extract_pinned_package(destination: Path) -> Path:
    data = ARCHIVE.read_bytes()
    if sha256(data) != ARCHIVE_SHA256:
        raise ValueError("Pinned data-ordlist archive hash changed")
    with tarfile.open(ARCHIVE, "r:gz") as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            if (name.is_absolute() or ".." in name.parts or not name.parts
                    or name.parts[0] != PACKAGE_DIR
                    or not (member.isfile() or member.isdir())):
                raise ValueError(f"Unsafe or unexpected package archive entry: {member.name}")
            path = destination.joinpath(*name.parts)
            if member.isdir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(member)
                if source is None:
                    raise ValueError(f"Could not read package archive entry: {member.name}")
                path.write_bytes(source.read())
    package = destination / PACKAGE_DIR
    upstream = package / "Data/List/Ordered.hs"
    if sha256(upstream.read_bytes()) != MODULE_SHA256:
        raise ValueError("Pinned Data.List.Ordered source hash changed")
    if not (package / "data-ordlist.cabal").is_file():
        raise ValueError("Pinned archive lacks its Cabal package definition")
    return package


def function_body(source: str, name: str) -> str:
    match = re.search(r"^" + name + r" ::.*?(?=\n\n)", source,
                      re.MULTILINE | re.DOTALL)
    if match is None:
        raise ValueError(f"Missing source-exact function {name}")
    return match.group(0)


def check_source_slice(package: Path) -> None:
    upstream = (package / "Data/List/Ordered.hs").read_text()
    pilot = PILOT.read_text()
    for name in FUNCTIONS:
        if function_body(upstream, name) != function_body(pilot, name):
            raise ValueError(f"Pilot function differs from pinned Cabal package: {name}")


PACKAGE_WRAPPER = """module PackageSubject where
import qualified Data.List.Ordered as O
isSortedInt :: [Int] -> Bool
isSortedInt = O.isSortedBy (<=)
memberInt :: Int -> [Int] -> Bool
memberInt = O.memberBy compare
insertSetInt :: Int -> [Int] -> [Int]
insertSetInt = O.insertSetBy compare
unionInt :: [Int] -> [Int] -> [Int]
unionInt = O.unionBy compare
mergeInt :: [Int] -> [Int] -> [Int]
mergeInt = O.mergeBy compare
"""


def execute_oracle(module: str, cases: list[dict], directory: Path,
                   package: Path | None, env: dict[str, str], deadline: float) -> dict[str, str]:
    directory.mkdir(parents=True)
    runner = directory / "Main.hs"
    runner.write_text(haskell_runner(module, cases))
    executable = directory / "oracle"
    args = ["ghc-9.2.7", "-ignore-dot-ghci", "-fforce-recomp", "-v0",
            "-odir", str(directory), "-hidir", str(directory)]
    if package is None:
        args += ["-i" + str(PILOT.parent)]
    else:
        (directory / "PackageSubject.hs").write_text(PACKAGE_WRAPPER)
        args += ["-package", "data-ordlist", "-i" + str(directory)]
    args += [str(runner), "-o", str(executable)]
    if package is not None:
        args = ["cabal", "exec", "--with-compiler", "ghc-9.2.7", "--"] + args
    require(run(args, cwd=package or directory, env=env, deadline=deadline,
                phase=f"{module}-build"), f"{module}-build")
    output = require(run([str(executable)], cwd=directory, env=env, deadline=deadline,
                         phase=f"{module}-run"), f"{module}-run")
    return parse_runner_output(output, [case["id"] for case in cases], module)


def check(config_path: Path, report_path: Path, timeout: float) -> int:
    config = load_config(config_path)
    suites = [suite for suite in config["suites"] if suite["module"] == "OrderedPilot"]
    if len(suites) != 1:
        raise ValueError("Expected exactly one OrderedPilot differential suite")
    cases = expand_cases(config, suites[0])
    env = tool_env()
    env.pop("GHC_PACKAGE_PATH", None)  # Cabal manages its own package database.
    deadline = time.monotonic() + timeout
    with tempfile.TemporaryDirectory(prefix="ordlist-package-fidelity-") as temp:
        work = Path(temp)
        package = extract_pinned_package(work)
        check_source_slice(package)
        require(run(["cabal", "build", "--offline", "--with-compiler", "ghc-9.2.7"],
                    cwd=package, env=env, deadline=deadline, phase="package-build"),
                "package-build")
        pilot = execute_oracle("OrderedPilot", cases, work / "pilot", None, env, deadline)
        upstream = execute_oracle("PackageSubject", cases, work / "package-oracle",
                                  package, env, deadline)
    mismatches = [{"id": case["id"], "pilot": pilot[case["id"]],
                   "package": upstream[case["id"]]}
                  for case in cases if pilot[case["id"]] != upstream[case["id"]]]
    report = {"package": "data-ordlist", "version": "0.4.7.0",
              "archiveSha256": ARCHIVE_SHA256, "moduleSha256": MODULE_SHA256,
              "cases": len(cases), "matched": len(cases) - len(mismatches),
              "mismatches": mismatches}
    atomic_write(report_path, json.dumps(report, indent=2) + "\n")
    if mismatches:
        print(f"Package fidelity failed: {len(mismatches)}/{len(cases)} mismatches",
              file=sys.stderr)
        return 1
    print(f"Package fidelity passed: {len(cases)}/{len(cases)} pilot/package executions matched")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=REPO / "tests/differential.json")
    parser.add_argument("--report", type=Path, default=REPO / ".lake/ordlist-package-fidelity.json")
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    try:
        return check(args.config, args.report, args.timeout)
    except (OSError, ValueError, PipelineError) as exc:
        print(f"Package fidelity error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
