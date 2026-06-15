# Design: first-class `{- @lean … -}` comments (source plugin) + gutter-icon / CodeLens UX

Date: 2026-06-15
Status: approved (pending spec review)

## Motivation

Two things, both from looking at the rendered `[lean| … |]` result in the editor:

1. **Notation.** `[lean| … |]` works but forces `import Lean.Spec`, the `QuasiQuotes`/`TemplateHaskell` pragmas, and a `lean-spec` dep into every spec'd module. A `{- @lean … -}` block comment reads more cleanly and needs none of that — *if* it can be extracted first-class (real source spans, no fragile regex). It can, via a GHC source plugin.
2. **UX.** The current verification feedback is a green/red **wavy underline spanning the whole block**, which is noisy. The user wants (a) a small **gutter icon** instead of the underline, and (b) the blaster **counterexample shown persistently** above a falsified property.

## Decisions (from brainstorming)

- **Coexist**, don't replace: keep the `[lean| |]` quasi-quoter AND add `{- @lean … -}` comments. Both feed the same `$LEAN_SPEC_DIR` mechanism, so the transpiler/map side is untouched.
- **Marker:** `{- @lean <lean text> -}` (the original marker, now read first-class).
- **Counterexample:** a **CodeLens** on the line above the property (not inline — VS Code has no virtual-line API).
- **Gutter icon** replaces the wavy underline; overview-ruler tick stays.

## Goals / Non-goals

Goals: comment notation extracted first-class (spans, no regex); no import/pragma/dep in comment-only files; gutter-icon feedback; persistent counterexample via CodeLens. Non-goals: GHC type-checking of the comment text (stays opaque Lean); removing the quasi-quoter; clickable CodeLens actions beyond display.

## Constraint

Pinned **GHC 9.2.7**. Comments are discarded by the parser unless the raw token stream is kept (`-fkeep-raw-token-stream` / `Opt_KeepRawTokenStream`); the source plugin relies on that.

## Design

### Source plugin — new in-repo package `shim/spec-plugin`, module `GhcSpecDump`
A GHC **source plugin** exposing `parsedResultAction`. transpile.sh injects it globally via the sandbox `ghc-options`: `-fkeep-raw-token-stream -fplugin GhcSpecDump` (alongside `GhcDump.Plugin`/`GhcDeclDump`). So **user files need no import/pragma/dep**.

`parsedResultAction` receives the `HsParsedModule` with retained comments. The plugin:
1. Collects block comments from the parsed result (GHC 9.2: the comments hang off the module's `EpAnnComments`/`ApiAnns`; gather both attached and "rogue" comments).
2. Keeps those whose text matches `{- @lean … -}` (after the `{-`, optional whitespace, the literal `@lean`).
3. For each: take its `RealSrcSpan` → `(startLine, endLine)`; strip the `{-` / `@lean` / `-}` wrapper and surrounding whitespace; `runIO`-write the inner Lean text to `$LEAN_SPEC_DIR/<Module>/<startLine>-<endLine>.lean`. `<Module>` is the dotted module name as a single flat directory component — **byte-identical contract to the `lean` quasi-quoter** (so the transpiler reads both transparently). No-op when `LEAN_SPEC_DIR` is unset.

New package depends only on `ghc` + `base` + `directory` + `filepath`; has its own `cabal.project` (`with-compiler: ghc-9.2.7`) matching the sibling plugin convention.

### Reused unchanged
- `Main.lean` `loadSpecs` + theorem emission + `.map.json` writer.
- `Emit.resolveSpecText` (type/ctor resolution applied to spec text).
- `transpile.sh`: `LEAN_SPEC_DIR` clear, staged-module force-recompile, the per-module emit loop.
- The `lean-spec` quasi-quoter package (kept for `[lean| |]`).

### transpile.sh
Add `spec-plugin` to the sandbox `build-depends`, `${REPO}/shim/spec-plugin` to `cabal.project packages`, and `-fkeep-raw-token-stream -fplugin GhcSpecDump` to `ghc-options`. Nothing else changes (force-recompile already guarantees the plugin re-fires each run).

### VS Code extension
Refactor the current "apply success/failure squiggle decorations" step into: **compute per-block outcomes** (valid / falsified + counterexample text, from the Lean diagnostics the extension already collects and maps via `.map.json`) → drive two consumers:
- **#2 Gutter icons:** two `createTextEditorDecorationType({ gutterIconPath, gutterIconSize, overviewRulerColor, overviewRulerLane })` — green ✓ and red ✗ SVG assets (added under `vscode-extension/media/`). Applied to the **first line** of each block by outcome. Remove the `textDecoration: 'underline wavy …'`. Keep the overview-ruler tick.
- **#3 CodeLens:** a `vscode.languages.registerCodeLensProvider({ language: 'haskell' })`. `provideCodeLenses` returns, per block, a CodeLens on the line above `block.hs[0]`: title `✗ Falsified — <counterexample>` (failure) or `✓ Valid` (pass). The counterexample string is the per-block outcome's diagnostic text, compacted to one line. No command action (display-only) for v1. The provider re-emits when outcomes change (fire `onDidChangeCodeLenses`).

Outcomes are cached per `.hs` URI (the extension already caches decoration state per URI and re-applies on editor switch), so the gutter icons and CodeLenses are "always there" when the file is reopened.

## Data flow (comment path)
```
.hs  {- @lean … -}  --GHC parse (-fkeep-raw-token-stream)--> retained comments
     --GhcSpecDump parsedResultAction--> $LEAN_SPEC_DIR/<Module>/<s>-<e>.lean (runIO)
     --[identical to quasi-quoter from here]-->
     transpiler loadSpecs → theorem in namespace + <out>.map.json → lake build (blaster)
     --extension--> per-block outcomes → gutter icons + CodeLens(counterexample)
```

## Testing / acceptance
- A module with only `{- @lean … -}` (no import, no pragma, no dep) dumps the right `<s>-<e>.lean` and round-trips to a `✅ Valid` theorem.
- Coexistence: a file with both a `{- @lean -}` and a `[lean| |]` block emits both theorems with correct, distinct map ranges.
- Span correctness: the `.map.json` `hs` range covers the comment's opener→closer lines.
- Extension: a passing property shows a green gutter ✓ and a `✓ Valid` CodeLens; a falsified one (e.g. OperatorCommons with `maxFee > 0` commented out) shows a red gutter ✗ and a CodeLens carrying the counterexample; both persist across editor switches; no wavy underline remains.
- Whole-project `lake build` stays green.

## Risks / open items
- GHC 9.2 comment access from `parsedResultAction` — the exact field (`hpm_annotations` vs `EpAnnComments` on the parsed module) must be confirmed against the 9.2.7 API; gather both attached and rogue comments. Fallback if comment retrieval is awkward: enable `Opt_KeepRawTokenStream` from the plugin's `driverPlugin` rather than relying solely on the `ghc-options` flag.
- CodeLens counterexample text: Lean/blaster emits a multi-line counterexample; compact to a single line for the lens title (full text remains in the Problems panel / hover via the existing diagnostic path).
