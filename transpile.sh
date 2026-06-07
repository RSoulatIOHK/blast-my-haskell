#!/usr/bin/env bash
#
# Run the GHC Core → Lean pipeline end-to-end on a single Haskell module.
#
# Usage:
#   ./transpile.sh <Source.hs> [output.lean]
#
# What it does:
#   1. Stages the .hs file in a per-repo sandbox (.transpile-sandbox/), with
#      a generated cabal file pinned to GHC 9.2.7 + ghc-dump-core.
#   2. cabal-builds it; the ghc-dump-core plugin produces .cbor dumps.
#   3. Runs the Haskell shim on pass-0000.cbor → JSON.
#   4. Runs ghccoretolean on the JSON → .lean source.
#
# The result is NOT auto-imported into the lake project. Wrap it in a
# namespace, add `#blaster [ … ]`, drop it under GhcCoreToLean/Spike/,
# import from GhcCoreToLean.lean, then `lake build`.

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

# The Haskell module name must come from the `module X where` declaration —
# not the filename, which can be lowercase (cabal rejects lowercase module ids).
MODNAME="$(grep -E '^[[:space:]]*module[[:space:]]+[A-Z][A-Za-z0-9_.]*' "$SRC" \
           | head -1 \
           | sed -E 's/^[[:space:]]*module[[:space:]]+([A-Z][A-Za-z0-9_.]*).*/\1/')"
if [[ -z "$MODNAME" ]]; then
  echo "could not find a 'module X where' declaration in $SRC" >&2
  exit 1
fi
MODLOWER="$(echo "$MODNAME" | tr '[:upper:]' '[:lower:]')"
OUT="${2:-/tmp/${MODLOWER}_out.lean}"

SANDBOX="${REPO}/.transpile-sandbox"
mkdir -p "$SANDBOX"

# 1a. Stage the source, prepending the plugin pragma if it's missing.
cp -- "$SRC" "${SANDBOX}/${MODNAME}.hs"
if ! grep -q 'GhcDump.Plugin' "${SANDBOX}/${MODNAME}.hs"; then
  TMP="$(mktemp)"
  { echo '{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}'; cat "${SANDBOX}/${MODNAME}.hs"; } >"$TMP"
  mv -- "$TMP" "${SANDBOX}/${MODNAME}.hs"
fi

# 1b. Write a fresh cabal file scoped to just this module. Always overwrite
# so MODNAME stays in sync with whichever source the user passed in.
cat >"${SANDBOX}/transpile-sandbox.cabal" <<EOF
cabal-version:      2.4
name:               transpile-sandbox
version:            0.1.0.0

library
    exposed-modules:    ${MODNAME}
    build-depends:      base, ghc-dump-core
    default-language:   Haskell2010
    hs-source-dirs:     .
EOF

cat >"${SANDBOX}/cabal.project" <<'EOF'
with-compiler: ghc-9.2.7

packages: .
EOF

# 2. cabal build (runs the ghc-dump-core plugin as a side effect).
echo "→ cabal build (GHC 9.2.7)"
( cd "$SANDBOX" && cabal build >/dev/null 2>&1 ) || {
  echo "  cabal build FAILED — re-running with output:" >&2
  ( cd "$SANDBOX" && cabal build ) >&2
  exit 1
}

# Find the desugarer-pass dump. The pipeline expects pass-0000 because later
# passes introduce worker-wrapper + GHC.Prim primops that the current Lower
# doesn't handle.
CBOR="$(find "${SANDBOX}/dist-newstyle" -name "${MODNAME}.pass-0000.cbor" -print -quit 2>/dev/null || true)"
if [[ -z "$CBOR" ]]; then
  echo "no ${MODNAME}.pass-0000.cbor produced — did the plugin pragma actually run?" >&2
  exit 1
fi

# 3. Find the shim binary (cabal puts it under an arch/ghc-version path).
SHIM="$(find "${REPO}/shim/dist-newstyle" -type f -perm -u+x -name ghc-core-shim 2>/dev/null | head -1 || true)"
if [[ -z "$SHIM" || ! -x "$SHIM" ]]; then
  echo "shim binary not built; run: ( cd shim && cabal build )" >&2
  exit 1
fi

# 4. The Lean exe is at a stable path under .lake/build/bin.
TRANSPILER="${REPO}/.lake/build/bin/ghccoretolean"
if [[ ! -x "$TRANSPILER" ]]; then
  echo "transpiler binary not built; run: lake build ghccoretolean" >&2
  exit 1
fi

JSON="/tmp/${MODLOWER}.json"
echo "→ shim         ${CBOR##*/}  →  ${JSON}"
"$SHIM" "$CBOR" >"$JSON"

echo "→ transpiler   ${JSON##*/}  →  ${OUT}"
"$TRANSPILER" "$JSON" "$OUT" >/dev/null

# Extract `{- @lean ... -}` annotation blocks from the original source and
# append them verbatim to the emitted .lean file. Use perl for reliable
# multi-line matching (BSD sed/awk on macOS don't make this easy).
ANNO="$(perl -0777 -ne '
  my $n = 0;
  while (/\{-\s*\@lean\s*(.*?)\s*-\}/sg) {
    print "\n", $1, "\n";
    $n++;
  }
  print STDERR "extracted $n \@lean block(s)\n" if $n > 0;
' "$SRC")"

if [[ -n "$ANNO" ]]; then
  printf '%s\n' "$ANNO" >>"$OUT"
fi

echo
echo "✓ wrote $OUT"
echo "  next: wrap in a \`namespace ${MODNAME}\` block,"
echo "        add a \`#blaster [ … ]\`, drop under GhcCoreToLean/Spike/,"
echo "        and \`lake build\`."
