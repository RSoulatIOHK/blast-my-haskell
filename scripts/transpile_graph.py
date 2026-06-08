#!/usr/bin/env python3
"""Orchestration helpers for transpile.sh's cross-module support.

Two subcommands, both line-oriented so bash can consume them:

  discover <entry.hs>
      Walk the local import graph starting from <entry.hs> and print, in
      dependency order (dependencies before dependents, entry last), one line
      per *local* module:

          <Module>\t<abs-source-path>\t<comma-separated local deps>

      "Local" = a module whose source file exists under the source root
      (the entry file's path minus its module path). Library/Prelude imports
      have no such file and are skipped.

  manifest <decls-dir> <Module>...
      Read <decls-dir>/<Module>.decls.json for each module and print

          <TypeName>\t<DefiningModule>

      one per declared data type. Used to resolve cross-module type refs
      (the transpiler reads this via EXT_TYPES_MANIFEST).
"""

from __future__ import annotations

import json
import os
import re
import sys

_MODULE_RE = re.compile(r"^\s*module\s+([A-Z][\w.']*)", re.M)
_IMPORT_RE = re.compile(r"^\s*import\s+(?:qualified\s+)?([A-Z][\w.']*)", re.M)


def _strip_comments(txt: str) -> str:
    # Block comments first (covers `{- @lean ... -}`), then line comments, so a
    # stray `import`/`module` token inside a comment can't be misread.
    txt = re.sub(r"\{-.*?-\}", "", txt, flags=re.S)
    txt = re.sub(r"--[^\n]*", "", txt)
    return txt


def _module_of(path: str) -> str | None:
    m = _MODULE_RE.search(_strip_comments(open(path).read()))
    return m.group(1) if m else None


def _imports_of(path: str) -> list[str]:
    return _IMPORT_RE.findall(_strip_comments(open(path).read()))


def _rel(mod: str) -> str:
    return mod.replace(".", "/") + ".hs"


def discover(entry: str) -> int:
    entry = os.path.abspath(entry)
    entry_mod = _module_of(entry)
    if entry_mod is None:
        print(f"transpile_graph: no `module` decl in {entry}", file=sys.stderr)
        return 1
    rel = _rel(entry_mod)
    if not entry.endswith(rel):
        print(
            f"transpile_graph: {entry} does not match module {entry_mod} "
            f"(expected path ending in {rel}); is the layout hierarchical?",
            file=sys.stderr,
        )
        return 1
    root = entry[: -len(rel)].rstrip("/")

    seen: dict[str, tuple[str, list[str]]] = {}
    order: list[str] = []

    def visit(mod: str) -> None:
        if mod in seen:
            return
        src = os.path.join(root, _rel(mod))
        if not os.path.isfile(src):
            return  # external (library/Prelude) — not transpiled
        seen[mod] = ("", [])  # placeholder guards against import cycles
        local_deps: list[str] = []
        for imp in _imports_of(src):
            if os.path.isfile(os.path.join(root, _rel(imp))):
                local_deps.append(imp)
                visit(imp)
        seen[mod] = (src, local_deps)
        order.append(mod)  # post-order ⇒ deps precede dependents

    visit(entry_mod)
    for mod in order:
        src, deps = seen[mod]
        print(f"{mod}\t{src}\t{','.join(deps)}")
    return 0


def manifest(decls_dir: str, mods: list[str]) -> int:
    for mod in mods:
        p = os.path.join(decls_dir, f"{mod}.decls.json")
        if not os.path.isfile(p):
            continue
        d = json.load(open(p))
        defining = d.get("module", mod)
        for t in d.get("typeDecls", []):
            name = t.get("name")
            if name:
                print(f"{name}\t{defining}")
    return 0


def main(argv: list[str]) -> int:
    if len(argv) >= 3 and argv[1] == "discover":
        return discover(argv[2])
    if len(argv) >= 3 and argv[1] == "manifest":
        return manifest(argv[2], argv[3:])
    print("usage: transpile_graph.py (discover <entry.hs> | "
          "manifest <decls-dir> <Module>...)", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
