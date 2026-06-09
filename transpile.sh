#!/usr/bin/env bash
#
# Run the GHC Core → Lean pipeline end-to-end on a Haskell module *and its
# local dependencies* (transitive `import`s that resolve to a .hs under the
# same source root). Library/Prelude imports are ignored.
#
# Usage:
#   ./transpile.sh <Source.hs> [output.lean]
#
# What it does:
#   1. Discovers the local import graph (scripts/transpile_graph.py).
#   2. Stages every local module in a sandbox (.transpile-sandbox/) under a
#      cabal pinned to GHC 9.2.7 + ghc-dump-core + the decl-dump plugin, and
#      cabal-builds once (dumping CBOR + decls for all modules).
#   3. For each module, in dependency order: shim CBOR → JSON, then
#      ghccoretolean → .lean (each wrapped in `namespace <Module>`, with
#      `import GhcCoreToLean.Generated.<Dep>` for local deps and a shared
#      type→module manifest so cross-module refs resolve).
#
# Dependencies land under GhcCoreToLean/Generated/<path>.lean; the entry
# module lands at [output.lean] (default Generated/<path>.lean). Then:
# `lake build` (lake sequences the dependency oleans from the import graph).

set -euo pipefail

SRC="${1:-}"
if [[ -z "$SRC" ]]; then
  echo "usage: $(basename "$0") <Source.hs> [output.lean]" >&2
  exit 1
fi
if [[ ! -f "$SRC" ]]; then
  echo "no such file: $SRC" >&2
  exit 1
fi

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HELPER="${REPO}/scripts/transpile_graph.py"
GENROOT="${REPO}/GhcCoreToLean/Generated"

# Entry module name (from the `module X where` decl, not the filename).
MODNAME="$(grep -E '^[[:space:]]*module[[:space:]]+[A-Z][A-Za-z0-9_.]*' "$SRC" \
           | head -1 \
           | sed -E 's/^[[:space:]]*module[[:space:]]+([A-Z][A-Za-z0-9_.]*).*/\1/')"
if [[ -z "$MODNAME" ]]; then
  echo "could not find a 'module X where' declaration in $SRC" >&2
  exit 1
fi

# Default the entry output under the lib so it inherits `import Blaster`
# resolution; the path mirrors the module so its Lean module name is stable.
OUT="${2:-${GENROOT}/${MODNAME//.//}.lean}"

SANDBOX="${REPO}/.transpile-sandbox"
mkdir -p "$SANDBOX/.decls"

# ---------------------------------------------------------------------------
# 1. Discover the local import graph (dependency order, deps before dependents).
MODULES=(); SRCS=(); DEPS=()
while IFS=$'\t' read -r m s d; do
  MODULES+=("$m"); SRCS+=("$s"); DEPS+=("$d")
done < <(python3 "$HELPER" discover "$SRC")
if [[ ${#MODULES[@]} -eq 0 ]]; then
  echo "no local modules discovered from $SRC" >&2
  exit 1
fi
echo "→ modules (dep order): ${MODULES[*]}"

# ---------------------------------------------------------------------------
# 2a. Stage every local module, mirroring its module path. The cabal
#     ghc-options inject both plugins, so no per-file pragma is required.
for i in "${!MODULES[@]}"; do
  rel="${MODULES[$i]//.//}.hs"
  dest="${SANDBOX}/${rel}"
  mkdir -p "$(dirname "$dest")"
  cp -- "${SRCS[$i]}" "$dest"
done

# 2b. Fresh cabal exposing all staged modules.
EXPOSED="$(IFS=,; echo "${MODULES[*]}")"
cat >"${SANDBOX}/transpile-sandbox.cabal" <<EOF
cabal-version:      2.4
name:               transpile-sandbox
version:            0.1.0.0

library
    exposed-modules:    ${EXPOSED}
    build-depends:      base, ghc-dump-core, decl-plugin, lean-spec
    default-language:   Haskell2010
    hs-source-dirs:     .
    ghc-options:        -fplugin GhcDump.Plugin -fplugin GhcDeclDump
EOF

cat >"${SANDBOX}/cabal.project" <<EOF
with-compiler: ghc-9.2.7

packages:
    .
    ${REPO}/shim/decl-plugin
    ${REPO}/shim/lean-spec
EOF

export GHC_DECL_DUMP_DIR="${SANDBOX}/.decls"
# Per-spec dump dir for the `lean` quasi-quoter. Cleared each run; the cp-staging
# of every source forces recompilation, so all specs re-dump fresh.
export LEAN_SPEC_DIR="${SANDBOX}/.leanspecs"
rm -rf "$LEAN_SPEC_DIR"
mkdir -p "$LEAN_SPEC_DIR"

# 2c. One cabal build (dumps CBOR + decls for every module).
echo "→ cabal build (GHC 9.2.7)"
( cd "$SANDBOX" && cabal build >/dev/null 2>&1 ) || {
  echo "  cabal build FAILED — re-running with output:" >&2
  ( cd "$SANDBOX" && cabal build ) >&2
  exit 1
}

# ---------------------------------------------------------------------------
# 3. Locate the shim + transpiler binaries.
SHIM="$(find "${REPO}/shim/dist-newstyle" -type f -perm -u+x -name ghc-core-shim 2>/dev/null | head -1 || true)"
if [[ -z "$SHIM" || ! -x "$SHIM" ]]; then
  echo "shim binary not built; run: ( cd shim && cabal build )" >&2
  exit 1
fi
TRANSPILER="${REPO}/.lake/build/bin/ghccoretolean"
if [[ ! -x "$TRANSPILER" ]]; then
  echo "transpiler binary not built; run: lake build ghccoretolean" >&2
  exit 1
fi

# 4. Shared type→module manifest (so external type refs resolve to <Mod>.<Type>).
MANIFEST="/tmp/transpile-ext-types.tsv"
python3 "$HELPER" manifest "${SANDBOX}/.decls" "${MODULES[@]}" > "$MANIFEST"
export EXT_TYPES_MANIFEST="$MANIFEST"

# ---------------------------------------------------------------------------
# Emit one module: shim → transpiler (namespace + imports + manifest + specs
# + source map) → close namespace.
emit_module() {
  local mod="$1" src="$2" deps="$3" out="$4"
  local cbor decls json lean_imports dep

  # ghc-dump-core names CBOR by module *path* (Lib.Inner → Lib/Inner.pass-0000.cbor),
  # whereas the decl plugin names by dotted module (Lib.Inner.decls.json).
  cbor="$(find "${SANDBOX}/dist-newstyle" -path "*/${mod//.//}.pass-0000.cbor" -print -quit 2>/dev/null || true)"
  if [[ -z "$cbor" ]]; then
    echo "no ${mod//.//}.pass-0000.cbor produced — did the plugin run for $mod?" >&2
    exit 1
  fi
  decls="${SANDBOX}/.decls/${mod}.decls.json"
  json="/tmp/transpile-${mod//./_}.json"
  if [[ -f "$decls" ]]; then
    "$SHIM" "$cbor" --decls "$decls" >"$json"
  else
    "$SHIM" "$cbor" >"$json"
  fi

  # Lean `import`s for this module's local dependencies.
  lean_imports=""
  if [[ -n "$deps" ]]; then
    IFS=',' read -ra _darr <<< "$deps"
    for dep in "${_darr[@]}"; do
      lean_imports+="GhcCoreToLean.Generated.${dep} "
    done
  fi

  mkdir -p "$(dirname "$out")"
  LEAN_IMPORTS="$lean_imports" "$TRANSPILER" "$json" "$out" "$mod" >/dev/null
  export DECLS_JSON_PATH="$decls"

  # Close the `namespace <module>` the transpiler opened (specs are already
  # emitted by the transpiler itself, inside the namespace).
  printf '\nend %s\n' "$mod" >>"$out"
}

# ---------------------------------------------------------------------------
# 5. Emit every module in dependency order. Dependencies → Generated/<path>;
#    the entry module → $OUT.
for i in "${!MODULES[@]}"; do
  mod="${MODULES[$i]}"
  if [[ "$mod" == "$MODNAME" ]]; then
    out="$OUT"
  else
    out="${GENROOT}/${mod//.//}.lean"
  fi
  echo "→ ${mod}  →  ${out}"
  emit_module "$mod" "${SRCS[$i]}" "${DEPS[$i]}" "$out"
done

echo
echo "✓ ${#MODULES[@]} module(s) transpiled (${MODULES[*]})"
# Machine-readable entry-output marker consumed by the VS Code extension
# (regex `wrote (\S+\.lean)`); the entry path must be the first token after it.
echo "wrote $OUT"
echo "  next: \`lake build\` (builds dependency oleans from the import graph)."
