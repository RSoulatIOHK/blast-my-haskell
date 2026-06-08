# Design: first-class `[lean| … |]` specs via a quasi-quoter + plugin annotations

Date: 2026-06-08
Status: approved (pending spec review)

## Motivation

Lean properties are currently written as magic block comments:

```haskell
{- @lean theorem foo : … := by blaster -}
```

`transpile.sh` extracts these with a perl regex (`/\{-\s*\@lean\s*(.*?)\s*-\}/`),
appends them verbatim to the generated `.lean`, and builds a `.map.json`
(line ranges) for the VS Code extension to forward diagnostics back. Problems:

- **Fragile.** Regex scraping; line ranges computed by counting; a stray
  `@lean` in unexpected text would misfire.
- **Not first-class.** The property is invisible to GHC — a "weird" comment
  bolted on, not a real entity with a source span.
- **No multi-function story beyond text.** (This one is actually fine as text,
  but we want the carrier to be principled.)

We want properties that are **robust** (driven by the real GHC AST, not
regex), **first-class** (real GHC entities with source spans), and able to
state **high-level properties over several functions at once** (a property is
module-level, naming any functions in scope — not bound to one declaration).

## Goals

- Replace `{- @lean … -}` with a first-class notation.
- Drive extraction from GHC annotations via the existing plugin (no regex).
- Multi-line authoring with no string escaping (unicode `∀`/`→`/`≤` etc.).
- Properties may reference several functions (module-level, in-scope).
- Keep the `.map.json` contract so the VS Code extension is unchanged.

## Non-goals

- GHC does **not** type-check the spec text; it stays opaque Lean (the symbols
  are checked later by Lean/blaster, as today).
- No editor syntax highlighting inside `[lean| |]`.
- No per-declaration attachment (specs are module-level by design).

## Constraint

Pinned compiler is **GHC 9.2.7** (no `MultilineStrings`, which arrived in
9.12). Hence a Template Haskell quasi-quoter (raw text) rather than a plain
`ANN` with a `String` literal (which would force `\n\`/`unlines` escaping).

## Design

### Author notation
```haskell
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
import Lean.Spec (lean)

[lean|
theorem addRatio_correct :
    ∀ (n1 d1 n2 d2 : Int), d1 > 0 → d2 > 0 →
    addRatio (CustomRatio.CustomRatio n1 d1) (CustomRatio.CustomRatio n2 d2)
      = CustomRatio.CustomRatio (n1 * d2 + n2 * d1) (d1 * d2) := by blaster
|]
```
A **top-level declaration** quasi-quoter. Raw multi-line text. Multiple blocks
per module allowed. References to imported symbols stay qualified
(`Ratio.addRatio`, `Ratio.CustomRatio`) exactly as in the cross-module rules.

### New package `lean-spec` (in-repo, GHC 9.2.7)
- `data LeanSpec = LeanSpec Int String deriving (Data, Typeable, ...)` — carries
  `(sourceLine, leanText)`.
- `lean :: QuasiQuoter`. Only `quoteDec` is defined (the others `error` with a
  clear message). `quoteDec txt` captures the splice line via `TH.location`
  (`loc_start . location`) and returns a single module-annotation declaration:
  ```haskell
  {-# ANN module (LeanSpec <line> <txt>) #-}
  ```
  i.e. `[PragmaD (AnnP ModuleAnnotation (… LeanSpec line txt …))]`. If a
  bare module annotation proves awkward to generate, fall back to a fresh
  dummy binding annotated with `LeanSpec` — decided in the plan.
- Added to the sandbox `build-depends` and `cabal.project packages`; user
  modules `import Lean.Spec`.

### Plugin: read annotations, dump specs
The existing `decl-plugin` (Core plugin; already dumps `typeDecls`/`instances`)
gains a pass that reads `mg_anns`, keeps `ModuleAnnTarget` annotations that
deserialize to `LeanSpec` (via `Data`), and emits them into the per-module
`.decls.json`:
```json
{ "module": "Ratio",
  "typeDecls": [...], "instances": [...],
  "leanSpecs": [ { "line": 17, "text": "theorem addRatio_correct : …" } ] }
```
`decl-plugin` depends on `lean-spec` for the `LeanSpec` type.

### Transpiler emits specs; perl scraping deleted
Specs already reach the transpiler because the shim merges `.decls.json` into
the program JSON. Changes:
- `Parse`/`AST`: carry `leanSpecs : List (Nat × String)` on the program.
- `Emit`/`Main`: after the binds/instances, emit each spec's text as-is
  **inside the `namespace`**, in line order. The existing `resolveUserCtors`
  post-pass now also covers spec text (qualifying `Ctor` → `Type.Ctor`).
- `Main` writes the `.map.json` itself, using each spec's captured Haskell line
  and the known emitted line offsets (same schema as today).
- `transpile.sh`: **delete** the `@lean` perl scrape + its map builder, **and**
  the ctor-rewrite perl pass (now handled in-transpiler). The per-module
  `end <Module>` append stays. The `wrote <entry>.lean` marker stays.

### VS Code extension
Unchanged. It still runs `transpile.sh`, parses `wrote …lean`, and reads
`<out>.map.json`. Only the *producer* of the map moves (perl → transpiler).

## Data flow (after)

```
.hs  [lean| … |]  --QuasiQuote(TH)-->  {-# ANN module (LeanSpec line txt) #-}
     --cabal build--> mg_anns
     --decl-plugin--> <Mod>.decls.json { leanSpecs: [{line,text}] }
     --shim (--decls)--> <mod>.json  (specs merged into program)
     --ghccoretolean--> Generated/<path>.lean  (theorems in namespace)
                        + <path>.lean.map.json  (built from captured lines)
     --lake build--> blaster verifies
```

## Migration
- Convert existing `{- @lean … -}` blocks in `Ratio.hs`, `OperatorCommons.hs`,
  `RatioSpec/MaxMinOverArithmetics.hs`, etc. to `[lean| … |]`, adding the
  `QuasiQuotes`/`TemplateHaskell` pragmas and `import Lean.Spec (lean)`.
- Keep the old perl path working until the new path is verified, then remove.

## Testing / acceptance
- A **multi-function** property (naming ≥2 functions) transpiles and proves.
- `.map.json` line ranges point at the correct `[lean| |]` source lines
  (diagnostic round-trips in the extension).
- Cross-module: a top-module spec calling through to an imported function still
  proves; `#print axioms` shows only `blasterProven` (no `sorryAx`).
- Whole-project `lake build` stays green.
- A deliberately false property is still `❌ Falsified` (soundness preserved).

## Risks / open items
- TH declaration-position annotation generation on 9.2.7 — confirm `AnnP
  ModuleAnnotation` works in `quoteDec`; fall back to dummy-binding ANN if not.
- Annotation deserialization in the Core plugin requires matching `lean-spec`
  package versions between user build and plugin (same in-repo package — OK).
- TemplateHaskell must be enabled in spec'd modules; the sandbox already injects
  plugins via `ghc-options`, but `QuasiQuotes`/`TemplateHaskell` are per-module
  `LANGUAGE` pragmas the user adds (document this).
