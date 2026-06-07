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

# Default the output under the GhcCoreToLean library so it inherits the lake
# project's `import Blaster` resolution. Files outside any declared lean_lib
# are not given the project's deps by the Lean LSP.
mkdir -p "${REPO}/GhcCoreToLean/Generated"
OUT="${2:-${REPO}/GhcCoreToLean/Generated/${MODNAME}.lean}"

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
# Two plugins are injected via ghc-options so user .hs files don't need any
# pragma:
#   * GhcDump.Plugin     — value bindings, dumps CBOR
#   * GhcDeclDump        — type & instance shapes (our plugin), dumps JSON
cat >"${SANDBOX}/transpile-sandbox.cabal" <<EOF
cabal-version:      2.4
name:               transpile-sandbox
version:            0.1.0.0

library
    exposed-modules:    ${MODNAME}
    build-depends:      base, ghc-dump-core, decl-plugin
    default-language:   Haskell2010
    hs-source-dirs:     .
    ghc-options:        -fplugin GhcDump.Plugin -fplugin GhcDeclDump
EOF

cat >"${SANDBOX}/cabal.project" <<EOF
with-compiler: ghc-9.2.7

packages:
    .
    ${REPO}/shim/decl-plugin
EOF

mkdir -p "${SANDBOX}/.decls"
export GHC_DECL_DUMP_DIR="${SANDBOX}/.decls"

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
DECLS_JSON="${SANDBOX}/.decls/${MODNAME}.decls.json"
echo "→ shim         ${CBOR##*/}  →  ${JSON}"
if [[ -f "$DECLS_JSON" ]]; then
  "$SHIM" "$CBOR" --decls "$DECLS_JSON" >"$JSON"
else
  "$SHIM" "$CBOR" >"$JSON"
fi

echo "→ transpiler   ${JSON##*/}  →  ${OUT}"
"$TRANSPILER" "$JSON" "$OUT" >/dev/null

export DECLS_JSON_PATH="$DECLS_JSON"

# Extract `{- @lean ... -}` annotation blocks from the original source,
# append them verbatim to the emitted .lean file, and emit a source map
# sidecar (${OUT}.map.json) listing each block's line range in both files.
# The map is what the VS Code extension uses to forward Lean diagnostics
# back onto the original Haskell annotation.
perl - "$SRC" "$OUT" <<'PERL_EOF'
use strict;
use warnings;
use JSON::PP;

my ($src_path, $out_path) = @ARGV;
my $map_path = "$out_path.map.json";

my $hs;
{
  local $/;  # slurp mode, scoped so the next file read stays line-oriented
  open(my $sfh, "<", $src_path) or die "open $src_path: $!";
  $hs = <$sfh>;
  close $sfh;
}

# Count existing lines in the .lean output (transpiler-produced part).
my $existing_lines = 0;
if (-e $out_path) {
  open(my $efh, "<", $out_path) or die "open $out_path: $!";
  while (<$efh>) { $existing_lines++ }
  close $efh;
}

my @blocks;
my $appended_lines = 0;

open(my $afh, ">>", $out_path) or die "append $out_path: $!";

while ($hs =~ /\{-\s*\@lean\s*(.*?)\s*-\}/sg) {
  my $match_start = $-[0];
  my $match_end   = $+[0];
  my $content     = $1;

  # Strip leading/trailing whitespace so the surrounding `{- @lean ... -}`
  # newlines don't pad the block.
  $content =~ s/\A\s+//;
  $content =~ s/\s+\z//;

  my $hs_start_line = 1 + (substr($hs, 0, $match_start) =~ tr/\n//);
  my $hs_end_line   = 1 + (substr($hs, 0, $match_end)   =~ tr/\n//);

  my $content_lines = 1 + ($content =~ tr/\n//);

  # Layout: one blank separator line, then content, then a terminator newline.
  print $afh "\n", $content, "\n";

  my $lean_start = $existing_lines + $appended_lines + 2;
  my $lean_end   = $lean_start + $content_lines - 1;

  push @blocks, {
    hs   => [$hs_start_line + 0, $hs_end_line + 0],
    lean => [$lean_start    + 0, $lean_end    + 0],
  };

  $appended_lines += 1 + $content_lines;
}
close $afh;

open(my $mfh, ">", $map_path) or die "write $map_path: $!";
print $mfh JSON::PP->new->canonical->pretty->encode({
  haskellPath => $src_path,
  leanPath    => $out_path,
  blocks      => \@blocks,
});
close $mfh;

my $n = scalar(@blocks);
print STDERR "extracted $n \@lean block(s); map: $map_path\n" if $n > 0;
PERL_EOF

# Final pass: rewrite Haskell-style ctor references (`Ctor`, used in user
# `@lean` annotations) to Lean-qualified form (`Type.Ctor`). The Lean
# transpiler already does this for code it emits; this catches the user's
# annotation text, which was appended *after* the transpiler ran. Rules are
# the same set as in Emit.lean's `resolveUserCtors` and are idempotent
# under non-overlapping `String.replace` semantics, so re-applying to the
# already-rewritten body produces no further changes.
if [[ -f "$DECLS_JSON" ]]; then
  perl - "$OUT" "$DECLS_JSON" <<'PERL_EOF'
use strict;
use warnings;
use JSON::PP;

my ($out_path, $decls_path) = @ARGV;

my $decls;
{
  local $/;
  open(my $df, "<", $decls_path) or die "open $decls_path: $!";
  $decls = decode_json(<$df>);
  close $df;
}

my @pairs;
for my $t (@{$decls->{typeDecls} || []}) {
  my $tn = $t->{name};
  for my $c (@{$t->{constructors} || []}) {
    push @pairs, [$tn, $c->{name}];
  }
}

exit 0 unless @pairs;

my $content;
{
  local $/;
  open(my $lf, "<", $out_path) or die "open $out_path: $!";
  $content = <$lf>;
  close $lf;
}

for my $p (@pairs) {
  my ($t, $c) = @$p;
  my $q = "$t.$c";
  # Match the rule set from Emit.lean's resolveUserCtors.
  # The pattern rule uses a negative lookahead so it does not match the
  # `| Ctor : <type>` ctor *declaration* inside the inductive block.
  $content =~ s/\Q| $c \E(?!:)/| $q /g;
  $content =~ s/\Q($c)\E/($q)/g;
  $content =~ s/ \Q$c\E \(/ $q (/g;
  $content =~ s/\(\Q$c\E \(/($q (/g;
}

open(my $wf, ">", $out_path) or die "write $out_path: $!";
print $wf $content;
close $wf;
PERL_EOF
fi

echo
echo "✓ wrote $OUT"
echo "  next: wrap in a \`namespace ${MODNAME}\` block,"
echo "        add a \`#blaster [ … ]\`, drop under GhcCoreToLean/Spike/,"
echo "        and \`lake build\`."
