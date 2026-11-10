#!/usr/bin/env python3
"""Export generated Lean for manual use; verification lives in verify.py."""
import argparse
import math
from pathlib import Path
import re
import sys
import tempfile
import time

from pipeline import PipelineError, cancel_on_termination, export, tool_env, transpile


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", nargs="?", type=Path)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--semantics", choices=["conservative", "approximate"], default="approximate")
    parser.add_argument("--roots", help="Comma-separated top-level Core bindings to translate")
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--timeout must be finite and positive")
    roots = args.roots.split(",") if args.roots is not None else None
    if roots is not None and (not roots or any(
            not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", root) for root in roots)):
        parser.error("--roots must be comma-separated Haskell function names")
    cancel_on_termination()
    try:
        with tempfile.TemporaryDirectory(prefix="ghccore-transpile-") as tmp:
            modules = transpile(args.source.resolve(), Path(tmp), tool_env(),
                                time.monotonic() + args.timeout, semantics=args.semantics,
                                roots=roots)
            for module in modules:
                if module["warnings"]:
                    print(module["warnings"], file=sys.stderr, end="")
            export(modules, args.output.resolve() if args.output else None)
        print("Transpiled Lean model. Use ./verify.sh for completed verification and a trust report.")
        return 0
    except PipelineError as exc:
        print(f"{exc.phase}: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    sys.exit(main())
