# Language-Coverage Roadmap — Design

**Date:** 2026-07-24
**Status:** Approved (user sign-off in brainstorming session)
**Execution:** Four milestones, each with its own implementation plan, developed
subagent-driven (Opus 4.8 implementers, TDD, reviewer subagents between tasks),
user checkpoint at each milestone boundary.

## Goal

Systematically close the transpiler's known-limitations list so ordinary
property-annotated Haskell transpiles and verifies end-to-end. Four feature
clusters, in order:

1. **M1 — Lists & tuples completion**
2. **M2 — Records & newtypes**
3. **M3 — Type-class completeness**
4. **M4 — Strings & Char**

M2–M4 are mutually independent; the order is frequency-of-use and can be
revised at any checkpoint. The toolchain stays pinned: GHC 9.2.7,
Lean `v4.24.0`, current Blaster.

## Non-goals

- Proof automation (induction generation for list/recursion theorems) — the
  existing rule stands: `by blaster` for quantifier-free arithmetic, manual
  `induction` proofs otherwise.
- Toolchain upgrades (newer GHC/Lean), IO/exotic primops, laziness modeling,
  `Show`/`Read`, GADTs/type families, multi-line UX work.
- Infinite structures: `iterate`, `repeat`, `cycle` remain **unmapped**
  (loud compile failure), documented.

## Principles (unchanged from prior milestones)

This is a *prover*, not just a compiler. Two failure modes:

- **Loud-fail (safe):** a dangling Lean name that won't compile — visible.
- **Silent-wrong (unsound):** compiles but encodes different semantics, so
  `by blaster` proves a theorem about the wrong function. **Never acceptable.**

Every mapping below is chosen so a wrong result is loud, never silent.
Haskell-partial functions route through the established bottom path
(`default` / `getD` + `Inhabited`), never to a total Lean function with
different semantics. Every new `valueMap`/`typeConMap`/`dataConMap` entry gets
(a) a `#guard` unit test and (b) coverage in at least one end-to-end fixture
with a `✅ Valid` property.

## Cross-cutting decision: runtime support module

**New file `GhcCoreToLean/Runtime.lean`** (namespace `Hs`) holding named helper
defs for any mapping too complex for a readable inline lambda — e.g.
`Hs.enumFromTo : Int → Int → List Int`. Generated files gain
`import GhcCoreToLean.Runtime` (emitted unconditionally; harmless when unused).
Trivial mappings stay inline in `Maps.lean` as today. Helpers are ordinary
Lean defs: unit-testable with `#guard`, stable named symbols for Blaster to
unfold, readable generated output.

---

## M1 — Lists & tuples completion

### List literals

`[a, b, c]` desugars in Core to `GHC.Base.build (\c n -> c a (c b (c c n)))`
where `build g = g (:) []`. `Lower` already erases type applications, so the
rank-2 argument needs no special handling:

- `GHC.Base.build` → `(fun g => g List.cons List.nil)`
- `GHC.Base.augment` → `(fun g xs => g List.cons xs)` (GHC emits it for
  `literal ++ xs` fusion forms)

### Enumerations

- `GHC.Enum.enumFromTo` (`[a..b]`) → `Hs.enumFromTo : Int → Int → List Int`
  in the runtime module (empty when `b < a`, matching Haskell).
- `enumFromThenTo` ( `[a,b..c]`) → `Hs.enumFromThenTo`, faithful to GHC's
  stride semantics including negative strides. `enumFrom`/`enumFromThen`
  (infinite) stay unmapped (loud).

### Tuple construction (3- and 4-)

- `dataConMap`: `(,,)` → `(fun a b c => (a, b, c))`, `(,,,)` → 4-ary analogue
  (qualified `GHC.Tuple.*` forms too). Plain left-application then works at
  any saturation — no Emit special-case needed.
- `typeConMap`: add `(,,,)` (4-tuple type). Patterns already work.

### List library additions (`valueMap`, qualified names only)

All verified against v4.24.0 names during implementation (e.g. flatten vs
join); Foldable/`GHC.List` name duality handled as for `length`/`foldr`.

| Haskell | Lean target | Notes |
|---|---|---|
| `take`, `drop` | `List.take`/`drop` ∘ `Int.toNat` | `toNat` clamps negatives to 0 — **matches** Haskell |
| `splitAt` | `Hs.splitAt` | pair result; `toNat` clamp matches |
| `replicate` | `List.replicate` ∘ `toNat` | clamp matches |
| `zip`, `zipWith`, `unzip` | `List.zip`/`zipWith`/`unzip` | zipWith arg order pinned by eta-wrap |
| `concat` | `List.flatten` | name-check on v4.24 |
| `concatMap` | `List.flatMap` | eta-wrap for arg order |
| `sum`, `product` | `List.sum`/`List.foldl (· * ·) 1` | Foldable-qualified names |
| `all`, `any`, `and`, `or` | `List.all`/`any`/`Hs.and`/`Hs.or` | Bool-returning |
| `elem`, `notElem` | via `List.contains`/negation | needs `BEq`; eta-wrap arg order |
| `lookup` | `Hs.lookup` | `List.lookup` exists but verify BEq/arg order |
| `maximum`, `minimum` | `Hs.maximumD default` route | **partial**: ⊥ on `[]` → bottom path + `Inhabited` |

### Fixtures

`ListLiterals.hs` (literals, ranges, ++ over literals), `ListLibrary.hs`
(the table above, one property per group), `TupleTriple.hs` (3/4-tuple
construction round-trip; unblocks the known TupleBasics follow-up).

---

## M2 — Records & newtypes

### Records (fixture-driven audit)

Record construction with field labels, record *update* (`r { f = v }`), and
selectors-as-functions all desugar to plain Core (constructor application /
case-and-rebuild / generated selector bindings). Hypothesis: mostly works
already. The milestone adds `RecordOps.hs` covering:

- named-field construction, multi-field update, selector used first-class
  (e.g. `map numerator xs`), cross-module selector use,

then fixes whatever breaks (expected: selector bindings for imported types,
possibly emission of GHC-generated selector defs). Scope is whatever the
fixture surfaces, not speculative work.

### Newtypes: full erasure

Decision: **erase**. Core already erases newtype constructors to coercions and
`Lower.lean` drops casts (`.cast e => lowerExpr e`), so values are erased
today; this milestone makes the type level agree:

- decl-plugin already dumps `kind: "newtype"` + field shape — the transpiler
  resolves the newtype tycon to its **underlying type** everywhere
  (`typeConMap` consult of decl info).
- Constructor and field selector map to identity.
- No Lean `structure` is emitted for a newtype.
- Theorems quantify over the underlying type (documented in README).

**Loud-fail guard:** a hand-written instance on a newtype (e.g. a different
`Eq` than the wrapped type's) is unrepresentable under erasure — the
transpiler must **error out** when decl/instance info shows one, not silently
use the underlying type's instance. `deriving` on newtypes is fine (it
coincides with the underlying instance).

Rejected alternative: preserve newtypes as one-field Lean structures. Requires
reconstructing wrap/unwrap at every erased cast site from coercion payloads
the shim currently discards (`ECoercion` carries no data) — significant shim +
Lower work, new soundness surface, little verification payoff.

### Fixtures

`RecordOps.hs`, `NewtypeBasic.hs` (newtype over Int with arithmetic property),
`NewtypeInstances.hs` (negative test: hand-written Eq on newtype → expected
transpiler error).

---

## M3 — Type-class completeness

Builds directly on the user-classes infrastructure (PR #2: `ClassDecl`
reconstruction, `methodMap`, instance emission).

### Superclasses

`class Eq a => C a where …`:

- Class emission: user-class superclass → `class C (a : Type) extends S a`;
  *builtin* superclass (`Eq`→`BEq`, `Ord`) → an instance-implicit field
  (`[BEq a]`) inside the class, since `extends` onto a builtin Lean class
  changes its instance surface. Requirement either way: method calls on the
  superclass resolve by instance inference.
- Core superclass dictionary selectors (`$p1C`, `$p2C`, …) are dict-producing:
  give their results dict role so `Lower`'s existing dict erasure removes
  them; the residual method selector then resolves via `methodMap` + Lean
  instances.
- Instance emission: the instance's superclass dict field is dropped (Lean
  finds the parent instance itself).

### Default methods

- Class decl: GHC emits `$dm<name>` top-level bindings for defaults. Transpile
  their bodies into `:= …` defaults inside the Lean `class` body.
- Instances whose dict field references `$dm<name>` **omit** that method in
  the emitted Lean `instance` (Lean fills the default in).

### Same-named methods across classes

Key `methodMap` by fully-qualified method name (module + class), not the bare
string, so two classes can both declare `size`. Emitted call sites are already
`Class.method`-qualified.

### Hand-written non-structural `Ord`

Reuse the hand-written-`Eq`→`BEq` translation path for `Ord`: from the
instance's `$ccompare` (and/or `$c<=`) body, emit `Ord`, `LE`, `LT` (and
`Min`/`Max` consistent with them) so e.g. an `Ord` on `CustomRatio` by
cross-multiplication is preserved rather than modeled structurally. Closes the
documented "hand-written Ord modeled structurally" unsoundness-adjacent gap.

### Multi-parameter classes (last; smallest real-world payoff)

- `ClassDecl` generalizes to a parameter *list*; emission
  `class C (a b : Type)`; constraints `C a b =>` → `[C a b]`; MPTC method
  call sites unchanged (`C.method`).
- Explicitly out of scope: functional dependencies, flexible instances beyond
  what Core hands us directly.

### Fixtures

`SuperClass.hs`, `DefaultMethods.hs`, `TwoClassesSameMethod.hs`,
`OrdHandwritten.hs` (cross-multiply Ord on a ratio type + ordering property),
`MultiParam.hs`.

---

## M4 — Strings & Char

### Shim fix (prerequisite)

`shim/Main.hs` currently discards string-literal contents
(`MachStr _ → "<bs>"`). Emit the actual bytes (UTF-8 decoded) in the JSON.
Parse side (`Parse.lean`) gains the `LitString` case.

### String = `List Char`

- Haskell `String` / `[Char]` → Lean `List Char` (already falls out of
  `typeConMap` `List` + `Char`). All M1 list operations compose (`++`,
  `length`, `take`, …) with no extra work.
- Core string literals arrive as `GHC.CString.unpackCString# "lit"#` — emit
  `"lit".toList` (Emit special-case on the applied literal; escaping handled
  by Lean string-literal quoting). `unpackCStringUtf8#` likewise.

### Char

- Char literals: shim/Parse `LitChar` case; the `C#` unwrapping already
  exists in `Lower`.
- `Data.Char.ord` → `(fun c => (c.toNat : Int))`.
- `Data.Char.chr` — **partial** (⊥ outside valid code points): route through
  the bottom path (`Hs.chrD`: valid → `Char.ofNat`, invalid → `default`),
  not raw `Char.ofNat` (which silently yields `'\0'`-adjacent behavior).
- Comparisons/equality on `Char` reuse the existing `decide`-wrapped Ord path.
- Small `Data.Char` predicate subset as demand requires: `isDigit`,
  `isAlpha`, `isSpace`, `isUpper`, `isLower`, `toUpper`, `toLower` — each only
  if Lean v4.24 has a semantics-matching counterpart (ASCII vs Unicode
  behavior verified per function; mismatch ⇒ `Hs.*` helper or unmapped/loud).

### Verification caveat (documented, not solved here)

Blaster's SMT encoding for `Char` may be weak or absent; string-heavy
properties may need manual Lean proofs. The milestone's deliverable is
**transpile fidelity** (fixtures compile, list-of-char properties with
arithmetic content verify), not new solver power.

### Fixtures

`StringBasics.hs` (literals, ++, length property), `CharOps.hs`
(ord/chr round-trip property with validity precondition).

---

## Execution model

Per milestone:

1. **Plan:** `superpowers:writing-plans` produces
   `docs/superpowers/plans/2026-07-24-m<N>-<topic>.md` (task-by-task,
   checkbox steps, exact commands).
2. **Branch:** `feature/m<N>-<topic>` off `main` (worktree isolation).
3. **Implement:** `superpowers:subagent-driven-development` — Opus 4.8
   implementer subagent per task under TDD; per-task gate:
   `lake build GhcCoreToLean` (runs `#guard`s) → `lake build ghccoretolean` →
   `./transpile.sh examples/haskell/<Fixture>.hs` →
   `lake build GhcCoreToLean.Generated.<Fixture>` shows `✅ Valid`.
   Reviewer subagent between tasks (spec compliance + code quality).
4. **Milestone gate:** full `lake build` (Spike examples still `✅ Valid`),
   README limitations section updated, `superpowers:requesting-code-review`,
   PR opened.
5. **User checkpoint:** review + merge decision before the next milestone.

## Risks

- **GHC name drift:** the desugarer's qualified names (`GHC.List.*` vs
  `Data.Foldable.*` vs `GHC.Base.*`) vary per function; every mapping is
  confirmed against an actual 9.2.7 Core dump before it lands (fixture-first).
- **Lean v4.24 API names** (`flatten`/`join`, `List.lookup` signature)
  verified by `#guard` at implementation time.
- **M2 unknowns:** records may surface selector-emission work not visible
  until the fixture runs; the milestone is scoped to what the fixture
  surfaces.
- **M3 dict shapes:** superclass/default dict layouts in Core are inferred
  from real dumps (as PR #2 did), not from GHC source reading; fixtures with
  unusual shapes fail loud.
