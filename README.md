# GhcCoreToLean — "blast my Haskell"

Transpile a Haskell module to **Lean 4** by way of its **GHC Core**, and verify
properties you embed in the Haskell source with the [Blaster](https://github.com/input-output-hk/Lean-blaster)
SMT tactic.

Verification currently establishes properties of a **translated Lean model**;
translation correctness is not certified. Use `./verify.sh` for completed checks
with explicit proof assumptions. Its default conservative policy refuses known
semantic approximations. `transpile.sh` remains available for model exploration.

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
# Check a mathematical-Integer example with an ordinary Lean proof.
./verify.sh tests/fixtures/verification/PureInteger.hs

# Check exact 64-bit Haskell Int overflow with an audited Lean proof.
./verify.sh tests/fixtures/verification/Overflow.hs

# Check strings and their exact machine-Int lengths.
./verify.sh examples/haskell/StringBasics.hs

# Opt into trusting Blaster's SMT results, which have no reconstructed proof.
./verify.sh examples/haskell/Arithmetic.hs --trust-smt

# Machine-readable result; exit 0 only when the selected policy accepts it.
./verify.sh tests/fixtures/verification/PureInteger.hs --json
```

The CLI builds and checks each local module in private temporary directories,
audits theorem dependencies, and checks that sources did not change during the
run. `proved` and `smt_valid` refer to the Lean model; `admitted`, `assumed`,
missing properties, errors, and timeouts never count as accepted verification.
See [verification policies and result format](docs/verification.md).

To export Lean files for manual work:

```bash
# Transpile one module (and its local imports, transitively) to Lean.
./transpile.sh examples/haskell/Ratio.hs
# → writes GhcCoreToLean/Generated/Ratio.lean (+ a .map.json sidecar)

# Elaborate the exported model (this alone does not audit proof assumptions).
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
- The text inside is **Lean 4**. Under the default conservative policy, Haskell
  `Int` maps to wrapping Lean `Int64`, while Haskell `Integer` maps to Lean
  `Int`. In a module that uses only Haskell `Int`, bare `Int` in an annotation
  is rewritten to `Int64` for compatibility. A module using both types must
  spell machine integers as `Int64` and mathematical integers as `Int`.
- `simp` can unfold generated definitions, and `Int64.add_assoc` /
  `Int64.add_comm` provide audited algebraic proofs. `bv_decide` is available,
  but Lean 4.24 reports compiler-trust axioms for it, so the verifier classifies
  such a theorem as `assumed` rather than accepting it silently.
- User data constructors are referenced as `T.C` (for example,
  `CustomRatio.CustomRatio`).
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

Three Lean lexical forms are **refused** inside a spec block, by name and before
anything is emitted: a **raw string** (`r"…"`), an **interpolated string**
(`s!"…"`), and a **guillemet identifier** (`«…»`). The constructor
auto-qualification above is a text rewrite guarded by a scanner that masks string
literals and comments; those three forms desync that mask, and the desync is
silent — a constructor name inside a *string literal* gets rewritten, so the
theorem elaborates and proves a property of a string nobody wrote (all three
measured). Ordinary literals and comments in spec text are fine and stay
verbatim. Must-fail fixture: `examples/haskell/SpecInterp.hs`.

## VS Code extension (optional)

`vscode-extension/` runs the audited `verify.sh --json` command and shows results
on each Haskell annotation with gutter icons, CodeLens, and hovers containing
theorem axioms and Lean diagnostics. Green denotes a proved property in an
accepted **Lean-model** run; SMT results remain amber and require explicit trust
for acceptance. Edits and newer runs invalidate older results. The defaults
are conservative semantics and no SMT trust; the Lean4 extension is optional.
See the [extension guide](vscode-extension/README.md) for settings and examples.

```bash
cd vscode-extension
npm install
npm run compile
npx @vscode/vsce package --no-dependencies --skip-license # → ghccoretolean-vscode-<ver>.vsix
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
  `Int#` primops are mapped. Conservative verification gives ordinary `Int`
  arithmetic, ranges, integral conversions, `gcd`/`lcm`, and statically safe
  division exact 64-bit semantics. Dynamic or exceptional divisors are refused.
  Exotic primops (string/array/IO) are not mapped.
- Mapped `base` surface: arithmetic (`+ - * negate abs signum`),
  integral (`quot rem div mod divMod quotRem gcd lcm fromIntegral fromInteger`),
  comparison/`Ord` (`== /= < <= > >= min max compare`/`Ordering`), booleans
  (`&& || not otherwise`), combinators (`id . const flip $`), the total list
  library (`++ map filter foldr foldl length reverse null take drop splitAt
  replicate zip zipWith unzip sum product all any and or elem notElem lookup
  concat concatMap`), list literals (`[a, b, c]`), list comprehensions
  (single- and multi-generator), `Int` ranges (`[a..b]`, `[a,b..c]` — the
  zero-stride `[a,a..c]` with `c ≥ a` is infinite in Haskell and the approximate
  model lowers it to `[]`, which changes finite observations such as `take 1`;
  conservative verification refuses stepped enumeration), 2-/3-/4-tuples
  (`fst snd`, construction, patterns), and
  `Maybe`/`Either` eliminators
  (`maybe fromMaybe isJust isNothing either`). Local recursive `where`/`let`
  helpers emit as Lean `let rec` (structural recursion only).
- **Strings and `Char`.** Haskell `String` and `[Char]` both transpile to Lean
  `List Char` — including the bare `String` *synonym*, which Core keeps in
  binder types. **String literals work.** Core spells a literal
  `GHC.CString.unpackCString# "lit"#` for a pure-ASCII literal and
  `GHC.CString.unpackCStringUtf8#` for one containing any non-ASCII character;
  both map to `String.toList`, so a literal's Lean image is a genuine
  `List Char` and the whole mapped list library composes with it. Quotes,
  backslashes and C0 control characters are escaped on emission (`\n`/`\t`/`\r`
  by name, the rest `\xNN`); non-ASCII is written raw into the UTF-8 output.
  NUL is faithful: GHC encodes it as modified UTF-8's overlong `C0 80`, which
  the shim repairs, so `"a\0b"` is 3 characters. `Char` literals work in both
  value and pattern position (`classify 'a' = 1`). The mapped `Char` surface is
  equality, ordering and `compare` (the ordinary `Ord` path), `ord`
  (→ `(fun c => (c.toNat : Int))`) and `isDigit` (→ `Char.isDigit`). Fixtures:
  `examples/haskell/StringBasics.hs`, `examples/haskell/CharOps.hs`. The gaps,
  all of them loud:
  - **`Data.Char` is not the name to look for.** Core records names from where
    a thing is *defined*, and `Data.Char` is a re-export module, so the
    mappable surface arrives as `GHC.Base.ord`, `GHC.Unicode.isDigit`,
    `GHC.Unicode.isAlpha`, `GHC.Char.chr` and so on. `Data.Char.*` is a
    0-occurrence spelling — worth knowing when reading a dump or a build error.
  - **Six Unicode functions are deliberately unmapped**: `isAlpha`, `isUpper`,
    `isLower`, `toUpper`, `toLower`, `isSpace`. Lean v4.24 is ASCII-only for
    *all* of them while Haskell is Unicode-aware (`isAlpha 'é'` is `True` in
    Haskell, `false` in Lean; `isSpace` differs on `\v`, `\f` and NBSP), so
    mapping any of them would compile and answer differently — the
    silent-wrong category. A faithful version needs `base`'s general-category
    tables. `isDigit` is mapped precisely because it is the one that agrees
    (both sides test ASCII 48–57, so the Unicode digit `'٥'` U+0665 is `False`
    on both).
  - **`chr` is unmapped.** A Haskell `Char` spans `[0, 0x10FFFF]` *including*
    the 2048 surrogate code points; a Lean `Char` excludes them. So `chr 0xD800`
    is a defined Haskell value with no Lean image, and no total Lean function is
    faithful — this is silent-wrongness, not the project's usual ⊥-refinement
    tradeoff. `ord` maps and `chr` does not, which is not an inconsistency:
    every *Lean* `Char` has a faithful Haskell image, so the gap enters only
    through construction.
  - **A literal containing a lone surrogate is refused by name**, rather than
    silently becoming U+FFFD. `String` and `Char` get separate messages
    carrying separate evidence, because the string case is a byte-encoding fact
    and the char case is not:

    ```
    string literal not representable: bytes `78 ed a0 80 79` in bind `lone`
    char literal not representable: code point `U+D800` in bind `lone`
    ```

    Transpilation exits nonzero and writes no `.lean`. Must-fail fixtures:
    `examples/haskell/StringSurrogate.hs`, `examples/haskell/CharSurrogate.hs`.
    NUL is *not* this case.
  - **`min`/`max` at `Char` fail loud** with `failed to synthesize Min Char` /
    `Max Char`: v4.24 has no such instance. The mapping itself is right at every
    type that does have one, so this is a `lake build` failure rather than a
    transpiler bug, and no instance is added. Every other binder the `Ord`
    recipe asks for does synthesize at `Char`, which is why equality and
    ordering work.
  - **`Char` ranges are safe only by accident.** `['a'..'e']` transpiles (rc=0)
    to `Hs.enumFromTo 'a' 'e'` and then fails loud at `lake build` only because
    that helper is monomorphic on `Int` (`GhcCoreToLean/Runtime.lean:20`):
    `'a' has type Char but is expected to have type Int`. Anyone generalising
    `Hs.enumFromTo` over an `Enum`-like class would silently route a `Char`
    range through Haskell's `chr`-based `Enum Char` — exactly the unfaithful
    direction above. Pin this before generalising.
- `error`/`undefined` are ⊥ on their whole domain, so they lower to Lean
  `default` in the approximate model. This does not establish preservation of
  Haskell behavior; conservative verification refuses these operations until
  their domains can be checked. The partial list/`Maybe` functions are ⊥
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
  `==`/`<=`/`<`/`min`/`max`. A hand-written *non-structural* `Ord` is now
  **preserved** — the old limitation ("would be modeled structurally") is
  closed. The route is chosen per instance by whether the `$ccompare` body
  contains a constructor-tag primop (`dataToTag#`/`tagToEnum#`): GHC emits one
  only in a *derived* `compare`, and only for a type with ≥3 nullary
  constructors, so those take Lean's `deriving Ord` while every other shape —
  hand-written, and derived on a type with ≤2 nullary constructors — is emitted
  from its own body, with `<`/`<=`/`min`/`max` derived from that `compare`. An
  instance defining both `compare` and a *disagreeing* `<` keeps the `compare`
  one: Lean resolves `Decidable (a < b)` only through `ltOfOrd`, so there is
  nowhere to wire a separate `<`. `Show`/`Read` are skipped (derived `Repr`
  prints counterexamples).
- **User-defined type classes** transpile, single- **and** multi-parameter:
  `class C a where …` / `class Convert a b where …` → Lean `class` with one
  `(v : Type)` binder per parameter; instances → Lean `instance`, including two
  *mirrored* instances of the same class (`Convert Celsius Fahrenheit` and
  `Convert Fahrenheit Celsius`, whose four `$c` binds collide by name in pairs
  and are attributed by unique); `C a =>` / `C a b =>` constraints →
  instance-implicit `[C a]` / `[C a b]`; and method calls → `C.method`. A
  multi-parameter call site works when the extra parameter is pinned by the
  signature (`aToB : A → B := Convert.conv`) or by the caller
  (`valB (Convert.conv x)`). The class *shape* (type parameters, superclasses,
  which methods carry defaults) comes from the decl plugin; the bodies are
  reconstructed from Core.
  - **Superclasses.** A *user*-class parent of a single-parameter class emits as
    Lean `extends`, and class decls are emitted in superclass-dependency order,
    so an instance of the child may omit the parent's fields entirely. A
    *builtin* parent (`Ord a => C a`) is injected at every **constraint site**
    instead of the class header, because `Ord`'s binder recipe contains
    `DecidableLT`/`DecidableLE` — plain `def`s, which `extends` rejects
    outright.
  - **Default methods.** A class default becomes a `:=` default in the Lean
    class body (translated from GHC's `$dm<method>` bind), and an instance that
    relies on it omits the field. An instance whose every method is defaulted
    emits as a fieldless `instance : C T where`.
  - **Builtin class constraints in signatures** are mapped (this closes the old
    "not yet supported" entry): `Eq a =>` → `[BEq t]`; `Ord a =>` → the
    eight-binder set `[Ord t] [LT t] [LE t] [DecidableLT t] [DecidableLE t]
    [Min t] [Max t] [BEq t]`, whose *order* is load-bearing (`DecidableLT t` is
    `DecidableRel (LT.lt …)` and only elaborates once `LT t` is bound; `BEq t`
    is in the set because Haskell's `Ord a` implies `Eq a`); and `Num a =>` →
    `[Add t] [Sub t] [Mul t] [Neg t]`. Only a constraint whose argument is a
    bare type *variable* is peeled — `Eq [a]` / `Eq Int` stays loud, and GHC
    passes no dictionary for a monomorphic signature anyway.

  What the class support does **not** cover — every item loud (warned at the
  transpiler, or failing at `lake build`, or both) except the one `dataToTag#`
  residual explicitly flagged as silent:
  - `Num a =>` reaches only the `+ - * negate` fragment. Any numeric
    **literal** under a `Num`-polymorphic def is loud, because `emitLiteral`
    ascribes literals to `Int`: `incr x = x + 1` fails with
    `failed to synthesize HAdd t Int t`, and an `OfNat` binder would not help —
    the ascription is the blocker. `abs`/`signum` are loud there too (their
    images test `a < 0`, which needs the `Ord` binder set a `Num` constraint
    does not supply). `Fractional`/`Integral`/`Real`/`Show`/`Enum` constraints
    are deliberately **unmapped** rather than approximated: the constraint arrow
    stays in the signature, the first value binder gets the dictionary's type,
    and the generated file does not elaborate — which is the signal that a new
    entry is wanted.
  - **Superclass drops, both warned.** A *multi-parameter* class loses **every**
    parent, and a *single-parameter* class whose parent is multi-parameter loses
    that parent. The plugin's `supers` channel records parent *names* without
    saying which parameter each one constrains, so `extends P ?` would be a
    guess. (`class Convert a b => C a` is rejected by GHC — `b` is not in scope
    — but `class Convert a a => C a` compiles in GHC 9.2.7, and that is the
    shape which reaches this.) Builtin-parent injection has its own consequence:
    the emitted class does **not** record the parent, so a class-body *default*
    using a parent operator is loud, and the emitted instance no longer
    re-checks the parent obligation Haskell imposed — weaker than Haskell, not
    wrong, since GHC already accepted the program.
  - **`Ord`.** A minimal instance defining only `<=` (or only `<`) is **refused
    with a warning** and gets no Lean `Ord` at all: its `compare` is GHC's
    dictionary-dependent class default, which needs `==` and `<=` from the very
    instance being defined. Nothing structural is substituted, so every
    `compare`/`<`/`min` at that type is loud. Same for a hand-written `compare`
    that recurses *and* calls another method of its own `Ord` (self-recursion
    **alone** is fine and is emitted). Mutually recursive types
    (`data A = ANil | A B; data B = B A deriving Ord`) would need one Lean
    `mutual` block, which this emitter does not produce: both instances are
    dropped with a warning and every use is loud (measured). A `compare` body
    calling a user top-level bind is a **forward reference** — the `Ord` block is
    spliced into the data block, ahead of every user bind — loud and warned. A
    `/=` at the instance's own head inside a spliced `$c==` body is warned (it
    resolves against the structural `BEq` the data block already carries). One
    residual is still **silently** structural: a literal `dataToTag#` written in
    a user `compare` under `MagicHash` reads as derived. That is measured, not
    hypothetical; closing it needs instance *origin* from the decl plugin, and a
    shape test on the derived body was rejected as fragile.
  - **Methods.** An instance that *overrides* a method with a body calling a
    **sibling** method of the same class is loud (`failed to synthesize C ?m`):
    GHC's `$c` body needs the instance's own dictionary, and the emitted def
    precedes the instance, which Lean does not see forward — a `mutual` block
    does not rescue it either. Superclass method calls inside an override hit
    the same wall; the fix is self-dispatch rewriting, which needs the
    dictionary argument `Lower` has already erased. Same-named methods across
    two classes are rejected by GHC itself within a module. Cross-module user
    classes remain unsupported: an imported class's method reference arrives
    module-qualified and misses the method map entirely, loud at `lake build`.
  - **Multi-parameter.** Functional dependencies and overlapping instances are
    unsupported, and the loudness is *upstream* of the transpiler: both need a
    `LANGUAGE` extension GHC will not assume, so a module using either is
    rejected before any dump exists. A call site where the extra parameter is
    determined by nothing (`f2 x = Convert.conv x`) is loud in Lean
    (`typeclass instance problem is stuck`) and rejected by GHC too, which wants
    `AllowAmbiguousTypes`.
  - The `$c/=` drop is now scoped to `Eq` instance heads, so a user class
    declaring `/=` (legal with `import Prelude hiding ((/=))`) keeps its method.
    If such a class's instance head **also** has an `Eq` instance, both `$c/=`
    binds carry that head type and both are dropped — that is now a **loud
    refusal** rather than silently emitting the builtin `!(a == b)`.
  - The `==` cell of that same family is **also refused**, and it is *not* the
    same mechanism — do not read the `/=` bullet as covering the operator-method
    family as a whole. A user class declaring `(==)` needs **no `hiding`
    pragma** at all (declaring the name is legal with `Prelude` in scope; only
    unqualified *uses* are ambiguous), and here **nothing is dropped**: GHC emits
    two `$c==` binds with the same name *and* the same first value-argument type,
    differing only by unique. The bind lookup keys on `(method, head type)` and
    not on the declaring class, so it took the first — measured, it wired
    `instance : BEq R` to the **user class's** body, emitted the derived
    structural body as dead code, and made `x == y` compute the user's operator:
    `decide` proved a Haskell falsehood with `rc=0` and empty stderr. The same
    collision reaches `compare` at an `Ord` head. Both are now refused by name,
    listing the method, the head, and **both** candidate classes
    (`examples/haskell/UserClassEqWithEq.hs`). This is a refusal rather than
    correct emission even though the instance *dictionaries* do carry the
    attribution: the emitter decides on that key in four independent head-only
    places, and threading uniques through some of them would move the wrong
    answer rather than remove it. Two instances of **one** class are unaffected —
    that is the case the head disambiguation exists for.
  - An instance method that resolves to nothing costs the **whole** instance
    (Lean cannot omit a field with no default). That skip is warned rather than
    refused, since every use site is already loud at `lake build`.
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
- Not yet supported: 5+-tuple construction; and the infinite list producers
  (`iterate`, `repeat`, `cycle`, `enumFrom`, `enumFromThen`) — all loud compile
  errors by design. Builtin type-class constraints in signatures
  (`Eq a => …`, `Ord a => …`, `Num a => …`) **are** supported now, with the
  `Num` gaps noted in the type-class bullet above; an *unmapped* constraint
  (`Fractional`, `Integral`, `Real`, `Show`, `Enum`) still fails loudly, with
  the dictionary surfacing as an unresolved `GHCCore.tyConOpaque` binder, and
  monomorphic code — e.g. the same function at `Int` — is unaffected either way.
  Goals that genuinely require induction over an unbounded list need a
  user-written `induction` proof. Bare `by blaster` (SMT) discharges
  quantifier-free arithmetic plus fixed-shape list/Bool goals — including ones
  quantified over element variables (`sumList [a] = a`) or over a list whose
  shape the statement fixes (`pairUp xs [] = []`). Concrete-value properties
  also close with `by decide`.
- **A property about a *recursive* definition is verified modulo an unproved
  termination argument.** Any def whose body references itself is emitted with
  `decreasing_by all_goals sorry` (`GhcCoreToLean/Emit.lean:769`): the
  transpiler supplies no termination argument at all, and does not attempt
  Lean's structural check. That `sorry` sits *inside the definition*, so it
  taints every theorem about it — the theorem depends on `sorryAx`, which
  yields `False`, and a `✅ Valid` on it therefore carries no logical guarantee
  on its own. `#print axioms` is how to check, and it is worth doing on any
  property you intend to rely on:

    ```
    #print axioms FibComplex.correct_fib
    -- 'FibComplex.correct_fib' depends on axioms: [sorryAx, Blaster.Tactic.blasterProven]
    #print axioms Ratio.falty_addRatio_commutative
    -- 'Ratio.falty_addRatio_commutative' depends on axioms: [Blaster.Tactic.blasterProven]
    ```

  A **non-recursive** def is unaffected: the second pair above is the clean case
  (`falty_addRatio_commutative` is about a non-recursive `addRatio`), and
  `Blaster.Tactic.blasterProven` is the solver's own axiom, not this one. To see
  which of your modules are affected, `grep decreasing_by` in the generated
  output; the recursive *def* itself reports `[sorryAx]` too
  (`#print axioms Ratio.gcdInt`). Note that the hazard is already handled in the
  one place it would be worst: the `Ord`/`Eq` bodies spliced into the data block
  are emitted with `recOverride := some false`, i.e. **no** `decreasing_by`, so
  no `sorry` can land under an instance and taint every `decide` proof about the
  order — those bodies must pass Lean's structural check instead, and fail loud
  if they cannot. Extending that to user defs — structural recursion where it
  holds, a measure where it does not, a loud failure otherwise — is a separate
  work item, not something this milestone claims.
- **Verification caveat at `Char` and `List Char`** (a solver limit, not a
  transpiler one — the milestone's deliverable is transpile fidelity). `Char`
  *scalars* verify well: equality, ordering, `compare` and a `Nat → Char → Nat`
  round-trip under a `n < 128` precondition are all `✅ Valid`
  (`examples/haskell/CharOps.hs`, five `blaster` theorems). Concrete `List Char`
  goals verify too (`['h','i'].length = 2`). But a goal quantified over a
  **symbolic** `List Char` fails under bare `by blaster` with
  `Inductive datatype with instance parameters not supported: 'BitVec`
  (measured on four goal shapes), and so does anything forcing `Char`'s
  `val : UInt32` representation (`c.toNat < 0x110000`). Wrapping the goal in
  `induction` rescues *some* of these but not all: it closes
  `(cs ++ ['!']).length = cs.length + 1` in both branches, yet on
  `StringBasics`'s own `shout_len` it closes `nil` and hits the same `BitVec`
  error in `cons` — which is why that fixture proves it by `simp`. So string
  properties should prefer `rfl`/`simp`. `by decide` is not an alternative at
  `Char`: it cannot quantify over it at all (`failed to synthesize Decidable
  (∀ (c : Char), …)`), though concrete `Char` data decides fine.
