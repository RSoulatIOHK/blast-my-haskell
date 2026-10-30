#!/usr/bin/env python3
"""Require the exact, unmodified Blaster revision recorded by Lake."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


REPO = Path(__file__).resolve().parents[1]


def main() -> int:
    manifest = json.loads((REPO / "lake-manifest.json").read_text())
    matches = [p for p in manifest["packages"] if p["name"] == "Blaster"]
    if len(matches) != 1 or not matches[0].get("rev"):
        print("Expected exactly one pinned Blaster dependency", file=sys.stderr)
        return 1
    checkout = REPO / ".lake/packages/Blaster"
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
        dirty = subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=checkout, text=True).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"Cannot inspect Blaster checkout: {exc}", file=sys.stderr)
        return 1
    if head != matches[0]["rev"] or dirty:
        print(f"Blaster checkout is not the clean pinned revision: {head}, dirty={bool(dirty)}",
              file=sys.stderr)
        return 1
    print(f"Blaster clean at {head}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
