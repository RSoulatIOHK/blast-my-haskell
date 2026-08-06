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
- For **imported** symbols, qualify with the module **by hand** — nothing in the
  pipeline qualifies hand-written spec text. A value is `M.f`
  (`RecordOps.mkPoint`), a type is `M.T` (`Ratio.CustomRatio`), and a
  constructor is `M.T.C` (`Ratio.CustomRatio.CustomRatio`). A bare imported name
  is auto-bound by Lean as an implicit and then fails loudly (`function expected
  at mkPoint`).
- A **local** constructor is auto-qualified to `T.C`, but only where an argument
  makes the application unambiguous: a bracketed or numeric-literal argument
  fires (`Point (x) (y)`, `Point 1 2`, `Rect (Point 0 0) 1 1`) while a bare
  lowercase variable does **not** — `Point x y` stays bare and fails loudly
  (`function expected at Point`). So either parenthesise the arguments or write
  the qualified form yourself (`Point.Point x y`), which is what the example at
  the top of this README does. Lowercase is excluded on purpose: otherwise
  `instance : BEq CustomRatio where` would read `where` as an argument and
  rewrite a *type* to a constructor.

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
  library (`++ map filter foldr foldl length reverse null take drop splitAt
  replicate zip zipWith unzip sum product all any and or elem notElem lookup
  concat concatMap`), list literals (`[a, b, c]`), list comprehensions
  (single- and multi-generator), `Int` ranges (`[a..b]`, `[a,b..c]` — the
  zero-stride `[a,a..c]` with `c ≥ a` is infinite in Haskell and lowers to
  `default`), 2-/3-/4-tuples (`fst snd`, construction, patterns), and
  `Maybe`/`Either` eliminators
  (`maybe fromMaybe isJust isNothing either`). Local recursive `where`/`let`
  helpers emit as Lean `let rec` (structural recursion only).
- `error`/`undefined` are ⊥ on their whole domain, so they lower to Lean
  `default` (a total, sound bottom). The partial list/`Maybe` functions are ⊥
  on only *part* of their domain, so each lowers to a total Lean form that is
  faithful wherever Haskell is defined:
  - `head`, `last`, `maximum`, `minimum`, `fromJust` are ⊥ exactly on `[]` /
    `Nothing`, and lower to Lean's `*D`/`getD` forms — faithful on the defined
    domain (`head [1,2,3] = 1`) and `default` exactly where Haskell is ⊥.
  - `!!` is ⊥ on **any** out-of-range index, not just on the empty list. It
    lowers to `getD` after `Int.toNat`, so a too-large index gives `default`,
    but a *negative* index reads position 0 instead (`[7,8,9] !! (-1)` ↦ `7`).
    That is still sound under partial-correctness modeling — ⊥ may be refined
    by any value — but it is one more reason indexing properties must carry an
    in-range precondition.
  - `tail`/`init` need no default at all: they map to Lean's total
    `List.tail`/`List.dropLast`, whose value on `[]` is `[]`. That happens to
    coincide with the ⊥→`default` convention, since `default : List α = []`.

  Either way, properties should carry the preconditions that rule the ⊥ branch
  out (partial-correctness modeling).
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
- **Records** transpile. A `data T = T { f :: … }` declaration emits a
  Lean `inductive` plus one selector `def` per field, and these record shapes
  desugar to Core the transpiler already handles: labeled construction
  (`Point { px = x, py = y }`), record-update syntax single- and multi-field
  (`p { px = px p + d }`, `r { width = w, height = h }`), a record field of
  another user type, and selectors used as **first-class functions**
  (`map px ps`). No field-name residue survives into the Lean. Not yet
  exercised: strict fields and GND-derived selectors.
- **Newtypes are fully erased** to their underlying type — they emit no Lean
  declaration at all. GHC's own desugaring erases the *value* level (the
  wrap/unwrap coercions never reach the shim), and the transpiler's resolution
  passes erase the *type* level, so `newtype Age = Age Int` makes `Age` **be**
  `Int` and properties quantify over the underlying type
  (`∀ (n : Int), bumpAge n = n + 1`). This works **cross-module** when the
  underlying type is a builtin/mapped one (`Int`, `List Int`, `(Int × Int)`, …):
  the defining module publishes the erasure for the modules that import it.
  Three consequences, all of them loud (the second is broader than newtypes —
  cross-module `data` types share its root cause):
  - **No type-class instance on a newtype** — hand-written, `deriving`, or with
    the newtype nested anywhere in the instance head (`instance Eq (Celsius,
    Celsius)`, `instance Convert Int Celsius`) — is a **loud transpiler error**.
    An erased newtype has no Lean type to carry an instance, and both fallbacks
    are silently wrong: `instance Eq Celsius` would relocate onto `Int`, so
    every `==` on `Int` in the module (theorem text included) would quietly mean
    the newtype's equality; a hand-written `Ord` would vanish and Lean's own
    `Int` order would take over. Write the instance — and the properties —
    against the underlying type instead, or drop the clause. `deriving` cannot
    be exempted: GHC's `tcg_insts` records no derived-vs-hand-written origin.
    Note the asymmetry with `data` — a derived `Show` on a `data` type is simply
    skipped, but `newtype Tag = Tag Int deriving (Show)` is refused outright.
    One gap: an instance on a newtype imported from a module *outside* the
    current transpile graph (so it contributes no manifest entry) is invisible
    to the check, and fails at `lake build` instead.
  - **Type names must be unique across a module graph** — the root cause is not
    newtype-specific: the Core dump records type references *unqualified*, so an
    imported `Other.Tag` reaches the importing module's dump spelled exactly like
    that module's own `Tag`, and no resolution order can be better than a guess.
    Two boundaries follow, with *different* loudness:
    - A module declaring a type whose name is also declared by a type it imports
      through the graph is a **hard transpiler error** (nonzero exit, nothing
      emitted for that module, and the run aborts before any later one).
      Both kinds on both sides: local `data` or `newtype` against an
      imported `data` or `newtype`. Picking either side typechecks and is
      silently wrong — `foreignTag :: Other.Tag -> Other.Tag` over
      `newtype Tag = Tag Int` emitted as `List Int → List Int` because the
      importing module happened to declare its own `newtype Tag = Tag [Int]`.
      Rename one of the types. (Deliberately over-strict in one direction: the
      manifest is graph-wide rather than import-scoped, so two modules sharing a
      type name are refused even when neither imports the other.)
    - A clash recorded in the cross-module *manifest* — `newtype Key = Key Int`
      in one module and `newtype Key = Key [Int]` in another, or a `newtype` in
      one and a `data` type in another — is **not** a hard error: all of that
      name's manifest entries are dropped with a warning, so references to it
      then fail at `lake build` (its type reference stays opaque). Same remedy.
      Note that a normal `transpile.sh` run now hits the hard error above
      *first* — the second module to declare the name sees the first one's
      manifest entry and refuses — so this softer path is only reached with a
      hand-assembled or stale manifest. (Several modules publishing the *same*
      underlying are interchangeable and dedup silently, with no warning.)
  - **A newtype over a user-defined type is not yet erasable across module
    boundaries** — same-module use is fine. Only underlyings built entirely from
    mapped types are published to importers, because the local `Q` in
    `newtype Wrapper = Wrapper Q` means nothing in the importing module (it would
    need `M.Q` — qualified-underlying resolution, not implemented). An importer
    that mentions such a newtype fails at `lake build`.
- **Parameterized data types are not supported.** The decl plugin dumps a type's
  name, kind and constructors but no type *parameters*, so `data Box a = Box a`
  loses `a`: the field type collapses to `_Unknown` and the emitted
  `inductive Box where | Box : (GHCCore.tyConOpaque "_Unknown") → Box` fails
  loudly at `lake build` (transpilation itself exits 0). Data and `newtype`
  declarations must be monomorphic today.
- Not yet supported: 5+-tuple construction; the infinite list producers
  (`iterate`, `repeat`, `cycle`, `enumFrom`, `enumFromThen`) — all loud compile
  errors by design; and builtin type-class constraints in signatures
  (`Eq a => …`, `Ord a => …`, `Num a => …`). A polymorphic function carrying
  such a constraint fails loudly (the dictionary surfaces as an unresolved
  `GHCCore.tyConOpaque` binder); monomorphic code — e.g. the same function at
  `Int` — is unaffected. (User-defined classes *are* supported; see the bullet
  above.)
  Goals that genuinely require induction over an unbounded list need a
  user-written `induction` proof. Bare `by blaster` (SMT) discharges
  quantifier-free arithmetic plus fixed-shape list/Bool goals — including ones
  quantified over element variables (`sumList [a] = a`) or over a list whose
  shape the statement fixes (`pairUp xs [] = []`). Concrete-value properties
  also close with `by decide`.
