# GhcCoreToLean — "blast my Haskell"

Transpile a Haskell module to **Lean 4** by way of its **GHC Core**, and verify
properties you embed in the Haskell source with the [Blaster](https://github.com/input-output-hk/Lean-blaster)
SMT tactic.

You write ordinary Haskell plus a few property annotations:

```haskell
module Ratio where

data CustomRatio = CustomRatio { numerator :: Integer, denominator :: Integer }

addRatio :: CustomRatio -> CustomRatio -> CustomRatio
addRatio (CustomRatio n1 d1) (CustomRatio n2 d2) =
    CustomRatio (n1 * d2 + n2 * d1) (d1 * d2)

{- @lean
theorem addRatio_correct :
    ∀ (n1 d1 n2 d2 : Int), d1 > 0 → d2 > 0 →
    addRatio (CustomRatio.CustomRatio n1 d1) (CustomRatio.CustomRatio n2 d2)
      = CustomRatio.CustomRatio (n1 * d2 + n2 * d1) (d1 * d2) := by blaster
-}
```

…and the pipeline turns it into a Lean file whose theorems are discharged by `blaster`.

## How it works

```
your .hs ──(GHC 9.2.7 + ghc-dump-core)──▶ Core CBOR ──(shim)──▶ JSON
        └─(@lean / [lean| |] recorded by GHC plugins/quasi-quoter)─┐
JSON + recorded specs ──(ghccoretolean, Lean)──▶ Generated/<Module>.lean
        └──────────────(lake build → Blaster verifies)────────────┘
```

- **`ghc-dump-core`** dumps GHC's desugared Core. A small Haskell **shim**
  (`shim/`) converts it to JSON.
- A GHC plugin (`shim/decl-plugin`) dumps data-type / instance shapes.
- Property annotations are recorded first-class (see *Writing properties*).
- The Lean transpiler **`ghccoretolean`** emits `Generated/<Module>.lean`
  (wrapped in `namespace <Module>`), and `lake build` runs Blaster on each
  property.

## Quick start (devcontainer) — recommended

If you have Docker + the VS Code **Dev Containers** extension: open this repo in
VS Code and run **"Dev Containers: Reopen in Container"**. The container installs
the full toolchain (GHC 9.2.7, Lean v4.24.0, cabal, Python, Node), then its
`postCreate` runs `lake build`, builds the shim, and builds + installs this
project's VS Code extension. When it finishes, open any `examples/haskell/*.hs`
and run **"GHC Core → Lean: Verify"**. (First build takes a few minutes — it
compiles Blaster and both toolchains.)

Running natively instead? Follow Prerequisites + Build below, and use the
**"GHC Core → Lean: Check Environment"** command to see what's missing.

## Prerequisites

- **Lean 4** via [`elan`](https://github.com/leanprover/elan) — the toolchain is
  pinned in `lean-toolchain` (`leanprover/lean4:v4.24.0`); `lake` ships with it.
- **GHC 9.2.7 + cabal** via [`ghcup`](https://www.haskell.org/ghcup/) — the shim
  and plugins pin `ghc-9.2.7`. (cabal fetches `ghc-dump-core` etc. from Hackage.)
- **Python 3** — `transpile.sh` uses `scripts/transpile_graph.py` for import
  discovery.
- **Node.js + npm** — only for the optional VS Code extension.

## Build

```bash
# 1. Lean side: transpiler binary + Blaster dependency (also verifies the
#    committed Spike/ examples — each prints `✅ Valid`).
lake build

# 2. Haskell side: the Core→JSON shim binary.
( cd shim && cabal build )
```

That's it — the GHC plugins (`decl-plugin`, `lean-spec`, `spec-plugin`) are built
automatically the first time you run `transpile.sh` (it stages them in a sandbox).

## Usage

```bash
# Transpile one module (and its local imports, transitively) to Lean.
./transpile.sh examples/haskell/Ratio.hs
# → writes GhcCoreToLean/Generated/Ratio.lean (+ a .map.json sidecar)

# Verify it (Blaster discharges each property; look for ✅ Valid).
lake build GhcCoreToLean.Generated.Ratio
```

`transpile.sh` follows local `import`s under the source root (standard
hierarchical layout: `module A.B.C` ⇒ `A/B/C.hs`), transpiles each dependency to
`GhcCoreToLean/Generated/<path>.lean`, and emits `import` lines so Lean builds
them in order. Library/`Prelude` imports are ignored. (Generated files are
git-ignored — regenerate them with `transpile.sh`.)

## Writing properties

Two notations, interchangeable; both record the Lean property text first-class
(real source spans, no regex) and feed the same pipeline.

**Block comment** — no imports or pragmas needed (read by the `spec-plugin` GHC
source plugin):

```haskell
{- @lean
theorem foo : ∀ (x : Int), f x = x + 1 := by blaster
-}
```

**Quasi-quoter** — needs `{-# LANGUAGE QuasiQuotes #-}`, `{-# LANGUAGE TemplateHaskell #-}`,
and `import Lean.Spec (lean)`:

```haskell
[lean|
theorem bar : ∀ (x : Int), f (g x) = x := by blaster
|]
```

Notes:
- The text inside is **Lean 4**, proved `by blaster`. Haskell `Integer`/`Int`
  both map to Lean `Int`; user data constructors are referenced as `T.C`
  (e.g. `CustomRatio.CustomRatio`).
- A property may range over **several** functions, not just one.
- For **imported** symbols, qualify with the module: `Ratio.addRatio`,
  `Ratio.CustomRatio`.

## VS Code extension (optional)

`vscode-extension/` provides a "verify" command that runs the pipeline and shows
the outcome inline on your `.hs`: a gutter ✓/✗ on each property, a CodeLens
(`✓ Valid` / `✗ Falsified — <counterexample>`) above it, and the full Lean
diagnostic on hover.

```bash
cd vscode-extension
npm install
npm run compile
npx @vscode/vsce package --no-dependencies     # → ghccoretolean-vscode-<ver>.vsix
code --install-extension ghccoretolean-vscode-*.vsix --force
# then reload the VS Code window
```

(Or open `vscode-extension/` in VS Code and press F5 for an Extension
Development Host.)

## Repository layout

| Path | What |
|------|------|
| `Main.lean`, `GhcCoreToLean/` | the Lean transpiler (`ghccoretolean`) |
| `GhcCoreToLean/Spike/` | committed worked examples that build + verify |
| `GhcCoreToLean/Generated/` | transpiler output (git-ignored) |
| `shim/` | `ghc-core-shim` (Core→JSON) + GHC plugins (`decl-plugin`, `lean-spec`, `spec-plugin`) |
| `transpile.sh`, `scripts/` | end-to-end driver + import-graph discovery |
| `examples/haskell/` | sample input modules |
| `vscode-extension/` | the editor integration |
| `docs/superpowers/` | design specs and implementation plans |

## Limitations

- Pinned to GHC 9.2.7 (the Core dump format and plugin API are version-specific)
  and Lean `v4.24.0`.
- The pipeline consumes the `pass-0000` (desugarer) Core. Common unboxed
  `Int#` primops are mapped; exotic primops (string/array/IO) are not.
- Mapped `base` surface: arithmetic (`+ - * negate abs signum`),
  integral (`quot rem div mod divMod quotRem gcd lcm fromIntegral fromInteger`),
  comparison/`Ord` (`== /= < <= > >= min max compare`/`Ordering`), booleans
  (`&& || not otherwise`), combinators (`id . const flip $`), the total list
  library (`++ map filter foldr foldl length reverse null`), 2-tuples
  (`fst snd`, construction, patterns), and `Maybe`/`Either` eliminators
  (`maybe fromMaybe isJust isNothing either`). Local recursive `where`/`let`
  helpers emit as Lean `let rec` (structural recursion only).
- `error`/`undefined` are ⊥ on their whole domain, so they lower to Lean
  `default` (a total, sound bottom). The partial list/Maybe functions
  (`head`, `tail`, `init`, `last`, `!!`, `fromJust`) are ⊥ *only* on the
  empty list / `Nothing`, so they lower to Lean's total `*D`/`getD` forms:
  faithful on their defined domain (`head [1,2,3] = 1`) and `default` exactly
  where Haskell is ⊥. Either way, properties should carry the preconditions
  that rule the ⊥ branch out (partial-correctness modeling).
- Instances: hand-written `Eq` translates to `BEq` from its body (so
  non-structural equality like Ratio's cross-multiply is preserved); derived
  `Eq`/`Ord` are reconstructed via Lean `deriving DecidableEq, Ord` plus
  `LE`/`LT`/`Min`/`Max`, so user types with `deriving (Eq, Ord)` support
  `==`/`<=`/`<`/`min`/`max`. A hand-written *non-structural* `Ord` would be
  modeled structurally (a known limitation). `Show`/`Read` are skipped
  (derived `Repr` prints counterexamples).
- User-defined single-parameter type classes transpile: `class C a where …`
  → Lean `class`, instances → Lean `instance`, `C a =>` constraints →
  instance-implicit `[C a]`, and method calls → `C.method` — all reconstructed
  from Core (no GHC-plugin changes). Not yet: superclasses, multi-parameter
  classes, default methods, methods whose signature doesn't mention the class
  parameter, and same-named methods across classes.
- Not yet supported: 3-tuple *construction* (type and pattern work; a
  constructed 3-tuple is a loud compile error), and Haskell list-literal syntax
  (`[a, b, c]` desugars to `GHC.Base.build`).
  Theorems over lists/recursion need a user-written `induction` proof — bare
  `by blaster` (SMT) discharges only quantifier-free arithmetic goals.
