# Base-Library & Core-Construct Coverage (Tiers 1–2) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the transpiler accept the GHC `base` symbols and Core constructs that real property-annotated Haskell actually uses — leading with the corpus-confirmed gaps (`++`, tuples, list/Prelude combinators) and the one soundness bug (dropped case binder).

**Architecture:** Three classes of change. (1) **Mapping-table additions** in [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean) — pure `String → Option String` functions, unit-tested with `#guard`. (2) **Core-construct handling** in [GhcCoreToLean/Lower.lean](../../../GhcCoreToLean/Lower.lean) / [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — tested with `#guard` over hand-built AST values plus end-to-end example transpiles. (3) A new test file [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean) imported by the library root so `lake build` runs every check.

**Tech Stack:** Lean 4 (`v4.24.0`), `lake`; GHC 9.2.7 + cabal for end-to-end transpiles via `./transpile.sh`; Blaster for property verification.

**Soundness discipline (read first):** This is a *prover*, not just a compiler. Two failure modes:
- **Loud-fail (safe):** a dangling Lean name that won't compile — the user sees it.
- **Silent-wrong (unsound):** compiles but encodes different semantics, so `by blaster` proves a theorem about the wrong function.

Every mapping below is chosen so a wrong result is *loud*, never silent. Specifically: **Haskell partial functions (`head`, `tail`, `fromJust`, …) MUST route through the existing `error`→`default` bottom path, never to a total Lean function** (Task 5). And division/`gcd`/`fold` argument-order semantics must match GHC exactly (Tasks 3, 7).

**Per-task loop (from [memory](../../../.claude/projects/-Users-romainsoulat-ghcCore-to-lean/memory/transpiler-dev-loop.md)):** edit → `lake build GhcCoreToLean` (runs `#guard` checks; the binary rebuilds via `lake build ghccoretolean` when an end-to-end step needs it) → for end-to-end steps `./transpile.sh <file>` then `lake build GhcCoreToLean.Generated.<Module>`.

---

## File Structure

- **Create** [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean) — `#guard` unit checks for `Maps` + `Emit` (one section per task). Built because the root imports it.
- **Modify** [GhcCoreToLean.lean](../../../GhcCoreToLean.lean) — add `import GhcCoreToLean.Tests.Unit`.
- **Modify** [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean) — extend `valueMap`, `typeConMap`, `dataConMap`.
- **Modify** [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — tuple alt-patterns; case-binder binding; local `let rec`; bottom-routing for partials.
- **Modify** [GhcCoreToLean/Lower.lean](../../../GhcCoreToLean/Lower.lean) — case-binder occurrence handling (paired with Emit).
- **Create** `examples/haskell/TupleBasics.hs`, `examples/haskell/ListBasics.hs`, `examples/haskell/CaseBinder.hs`, `examples/haskell/LocalRec.hs` — end-to-end fixtures.

---

## Task 0: Test harness wiring

**Files:**
- Create: `GhcCoreToLean/Tests/Unit.lean`
- Modify: `GhcCoreToLean.lean`

- [ ] **Step 1: Create the test file with one passing sentinel guard**

```lean
import GhcCoreToLean.Maps
import GhcCoreToLean.Emit
import GhcCoreToLean.AST

namespace GhcCoreToLean.Tests
open GHCCore GHCCore.Maps GHCCore.Emit

-- Sentinel: proves the harness builds and `#guard` failures break the build.
#guard valueMap "GHC.Base.id" == some "id"

end GhcCoreToLean.Tests
```

- [ ] **Step 2: Wire it into the library root**

In [GhcCoreToLean.lean](../../../GhcCoreToLean.lean), add after the existing imports:

```lean
import GhcCoreToLean.Tests.Unit
```

- [ ] **Step 3: Build to verify the harness runs**

Run: `lake build GhcCoreToLean`
Expected: PASS (no `#guard` error).

- [ ] **Step 4: Prove guards bite — temporarily break the sentinel**

Change the sentinel to `#guard valueMap "GHC.Base.id" == some "WRONG"`, run `lake build GhcCoreToLean`.
Expected: FAIL with a `#guard` evaluation error. Then revert to `some "id"` and rebuild — PASS.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Tests/Unit.lean GhcCoreToLean.lean
git commit -m "test: add #guard unit-test harness for transpiler mappings"
```

---

## Task 1: Total list/Prelude combinators (`valueMap`)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean` (`valueMap`)
- Test: `GhcCoreToLean/Tests/Unit.lean`

Total (non-partial) combinators only. Partial ones (`head`, `tail`, …) are Task 5.

> ⚠️ **The GHC Core names below are unconfirmed and the `#guard`s cannot catch a wrong one** — `#guard valueMap "X" == some "Y"` only tests that the table returns `Y`, never that `X` is the name the desugarer actually emits. Post-FTP, `length`/`null`/`foldr`/`foldl`/`elem` are **`Foldable` methods**, so on a `[Int]` the desugarer very likely emits `Data.Foldable.length`, **not** `GHC.List.length` — mapping the wrong LHS yields the exact dangling-name bug this task is meant to fix. Step 0 below discovers the real names before anything is written.

- [ ] **Step 0: Discover the real Core names (discovery-first, like Task 2)**

Create `examples/haskell/PreludeNames.hs` exercising *every* function this task maps:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module PreludeNames where
    import Prelude
    probe :: [Int] -> [Int] -> ([Int], Int, Bool)
    probe xs ys =
      ( map (\x -> x + 1) (filter (\x -> x > 0) (reverse (xs ++ ys)))
      , foldr (+) 0 xs + foldl (+) 0 ys + length xs
      , (not (null xs) && otherwise) || const True (flip (-) 1 0) )
```

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/PreludeNames.hs` then read `GhcCoreToLean/Generated/PreludeNames.lean` **and** the pass-0000 Core dump it produced. **Record the exact qualified name for each function** (e.g. confirm whether it is `GHC.List.length` or `Data.Foldable.length`, `GHC.Base.foldr` or `Data.Foldable.foldr`). Use the *observed* names as the LHS in Steps 1 and 3 below — the names written there are the best guess, not authoritative.

- [ ] **Step 1: Write the failing guards** (LHS = names observed in Step 0)

Append to the `Tests` namespace in `Unit.lean`:

```lean
-- Task 1: total list/Prelude combinators
#guard valueMap "GHC.Base.++"        == some "List.append"
#guard valueMap "++"                 == some "List.append"
#guard valueMap "GHC.Base.map"       == some "List.map"
#guard valueMap "GHC.List.filter"    == some "List.filter"
#guard valueMap "GHC.List.length"    == some "List.length"
#guard valueMap "GHC.List.reverse"   == some "List.reverse"
#guard valueMap "GHC.List.null"      == some "List.isEmpty"
#guard valueMap "GHC.List.foldr"     == some "(fun f z xs => List.foldr f z xs)"
#guard valueMap "GHC.List.foldl"     == some "(fun f z xs => List.foldl f z xs)"
#guard valueMap "GHC.Classes.&&"     == some "(· && ·)"
#guard valueMap "&&"                 == some "(· && ·)"
#guard valueMap "GHC.Classes.||"     == some "(· || ·)"
#guard valueMap "GHC.Classes.not"    == some "not"
#guard valueMap "not"                == some "not"
#guard valueMap "GHC.Base.const"     == some "(Function.const _)"
#guard valueMap "GHC.Base.flip"      == some "(fun f a b => f b a)"
#guard valueMap "GHC.Base.$"         == some "(fun f x => f x)"
#guard valueMap "GHC.Base.otherwise" == some "true"
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL — each new `#guard` reports `none ≠ some …`.

- [ ] **Step 3: Implement — extend `valueMap`**

In [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean), add these arms to `valueMap` immediately **before** the final `| _ => none`:

```lean
  -- List library (total). Haskell `++`/`map`/… map directly to Lean `List.*`.
  -- `foldr`/`foldl` are eta-wrapped so their Haskell arg order (f, z, xs) is
  -- pinned explicitly — Lean's `List.foldl` takes (f, init, xs) too, but the
  -- wrapper documents the contract and guards against future signature drift.
  | "GHC.Base.++"      | "++"      => some "List.append"
  | "GHC.Base.map"     | "map"     => some "List.map"
  | "GHC.List.filter"  | "filter"  => some "List.filter"
  | "GHC.List.reverse" | "reverse" => some "List.reverse"
  -- Foldable methods (post-FTP). The desugarer resolves these through
  -- `Data.Foldable.*` on `[a]`, NOT `GHC.List.*` — include both forms so the
  -- mapping fires regardless of which name Step 0 observed. (Drop whichever
  -- form the dump shows is never produced, to keep the table honest.)
  | "Data.Foldable.length" | "GHC.List.length" | "length"  => some "List.length"
  | "Data.Foldable.null"   | "GHC.List.null"   | "null"    => some "List.isEmpty"
  | "Data.Foldable.foldr"  | "GHC.List.foldr"  | "foldr"   => some "(fun f z xs => List.foldr f z xs)"
  | "Data.Foldable.foldl"  | "GHC.List.foldl"  | "foldl"   => some "(fun f z xs => List.foldl f z xs)"
  -- Boolean / Prelude combinators.
  | "GHC.Classes.&&"   | "&&"      => some "(· && ·)"
  | "GHC.Classes.||"   | "||"      => some "(· || ·)"
  | "GHC.Classes.not"  | "not"     => some "not"
  | "GHC.Base.const"   | "const"   => some "(Function.const _)"
  | "GHC.Base.flip"    | "flip"    => some "(fun f a b => f b a)"
  | "GHC.Base.$"       | "$"       => some "(fun f x => f x)"
  | "GHC.Base.otherwise" | "otherwise" => some "true"
```

- [ ] **Step 4: Run to verify pass**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat: map total list/Prelude combinators (++ , map, filter, foldr/l, &&, not, const, flip)"
```

---

## Task 2: Tuples — type, constructor, pattern (discovery-first)

**Files:**
- Create: `examples/haskell/TupleBasics.hs`
- Modify: `GhcCoreToLean/Maps.lean` (`typeConMap`, `dataConMap`), `GhcCoreToLean/Emit.lean` (`emitAltPattern`)
- Test: `GhcCoreToLean/Tests/Unit.lean`

Tuples fail on three independent paths today (type → `tyConOpaque`, ctor → dangling local, pattern → sanitized garbage). The exact GHC ctor name the shim emits (`(,)` vs `GHC.Tuple.(,)` vs `Tuple2`) is **unconfirmed**, so this task discovers it first, then maps it.

- [ ] **Step 1: Create the discovery fixture**

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module TupleBasics where
    import Prelude

    swapPair :: (Int, Int) -> (Int, Int)
    swapPair p = (snd p, fst p)

    mkPair :: Int -> Int -> (Int, Int)
    mkPair a b = (a, b)

    firstOf :: (Int, Int) -> Int
    firstOf (x, _) = x
```

- [ ] **Step 2: Transpile and inspect the emitted names**

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/TupleBasics.hs`
Then read `GhcCoreToLean/Generated/TupleBasics.lean`.
Expected (pre-fix): the tuple **type** appears as `(GHCCore.tyConOpaque "<TUPLE_TYCON>")` and the **ctor**/**pattern** as a dangling sanitized name. **Record the exact `<TUPLE_TYCON>` string and the exact ctor name string** — they drive Steps 4–5. (If the shim already emits `Prod`/`×`, note that and skip the corresponding map arm.)

- [ ] **Step 3: Write the failing guards** (substitute the strings observed in Step 2 for `(,)` if different)

```lean
-- Task 2: tuples. Replace "(,)" below with the exact name from Step 2 if it differs.
#guard typeConMap "(,)"  ["Int", "Int"]        == some "(Int × Int)"
#guard typeConMap "(,,)" ["Int", "Int", "Int"] == some "(Int × Int × Int)"
#guard dataConMap "(,)"  == some "Prod.mk"
-- alt-pattern for a 2-tuple binds both fields positionally
#guard emitAltPattern (.dataCon "(,)")
         [ {name := "x", unique := 1, ty := .tyCon "Int" [], role := .id},
           {name := "y", unique := 2, ty := .tyCon "Int" [], role := .id} ]
       == "(x_1, y_2)"
```

- [ ] **Step 4: Implement — `typeConMap` and `dataConMap`**

In [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean), add to `typeConMap` before `| _, _ => none` (use the exact tycon name(s) from Step 2; include both bare and qualified forms if the shim emits qualified):

```lean
  | "(,)",   [a, b]    => some s!"({a} × {b})"
  | "(,,)",  [a, b, c] => some s!"({a} × {b} × {c})"
```

Add to `dataConMap` before `| _ => none` (use the exact ctor name from Step 2):

```lean
  | "(,)"  | "(,,)" => some "Prod.mk"
```

> Note: `Prod.mk` is right-nested, so `(a, b, c)` Core-desugars to nested `(,)` applications and `Prod.mk a (Prod.mk b c)` matches Lean's `a × b × c = a × (b × c)`. If Step 2 shows GHC emits a *flat* 3-tuple ctor `(,,)` applied to three args, the `Prod.mk` mapping still works because emission applies it left-to-right; verify against the Step-2 output and adjust the arity handling in Step 5 if the pattern arity differs.

- [ ] **Step 5: Implement — tuple alt-pattern in `emitAltPattern`**

In [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean), `emitAltPattern`, add a tuple case to the `.dataCon name` branch (before the generic `let resolved := …`):

```lean
  | .dataCon name =>
    if name == "(,)" || name == "(,,)" then
      -- Tuple pattern: positional anonymous-constructor syntax `(a, b)`.
      let bs := String.intercalate ", " (bndrs.map localId)
      s!"({bs})"
    else
      let resolved := (dataConMap name).getD (sanitize name)
      if bndrs.isEmpty then resolved
      else
        let bs := String.intercalate " " (bndrs.map localId)
        s!"{resolved} {bs}"
```

- [ ] **Step 6: Run unit guards**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 7: End-to-end verify**

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/TupleBasics.hs && lake build GhcCoreToLean.Generated.TupleBasics`
Expected: PASS — `swapPair`/`mkPair`/`firstOf` compile; no `tyConOpaque` and no dangling `_lparen…` names remain in `GhcCoreToLean/Generated/TupleBasics.lean`.

- [ ] **Step 8: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/TupleBasics.hs
git commit -m "feat: support tuples (type, Prod.mk ctor, positional pattern)"
```

---

## Task 3: Num / Integral / Ord completion (`valueMap`, `typeConMap`, `dataConMap`)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean`
- Test: `GhcCoreToLean/Tests/Unit.lean`

Depends on Task 2 (`divMod`/`quotRem` return tuples). ⚠️ Watch silent-wrong: `Int.gcd`/`Int.lcm` return **`Nat`** in Lean while Haskell `gcd`/`lcm` return the numeric type — must coerce back to `Int`. Division rounding follows the existing [memory](../../../.claude/projects/-Users-romainsoulat-ghcCore-to-lean/memory/lean-int-division-semantics.md) (`tdiv`/`tmod` for quot/rem, `fdiv`/`fmod` for div/mod).

- [ ] **Step 1: Write the failing guards**

```lean
-- Task 3: Num/Integral/Ord completion
#guard valueMap "GHC.Num.fromInteger"    == some "id"
#guard valueMap "GHC.Real.toInteger"     == some "id"
#guard valueMap "GHC.Real.fromIntegral"  == some "id"
#guard valueMap "GHC.Num.signum"         == some "(fun a => if a < 0 then -1 else if a > 0 then 1 else 0)"
#guard valueMap "GHC.Real.divMod"        == some "(fun a b => (Int.fdiv a b, Int.fmod a b))"
#guard valueMap "GHC.Real.quotRem"       == some "(fun a b => (Int.tdiv a b, Int.tmod a b))"
#guard valueMap "GHC.Real.gcd"           == some "(fun a b => (Int.gcd a b : Int))"
#guard valueMap "GHC.Real.lcm"           == some "(fun a b => (Int.lcm a b : Int))"
#guard valueMap "GHC.Classes.compare"    == some "compare"
#guard typeConMap "Ordering" []          == some "Ordering"
#guard dataConMap "GHC.Types.LT"         == some "Ordering.lt"
#guard dataConMap "GHC.Types.EQ"         == some "Ordering.eq"
#guard dataConMap "GHC.Types.GT"         == some "Ordering.gt"
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL on the new guards.

- [ ] **Step 3: Implement — `valueMap` arms**

Add before `| _ => none` in `valueMap`:

```lean
  -- Integer/Int are both Lean `Int`, so the coercion methods are identities.
  | "GHC.Num.fromInteger"   | "fromInteger"   => some "id"
  | "GHC.Real.toInteger"    | "toInteger"     => some "id"
  | "GHC.Real.fromIntegral" | "fromIntegral"  => some "id"
  | "GHC.Num.signum"        | "signum"        =>
      some "(fun a => if a < 0 then -1 else if a > 0 then 1 else 0)"
  -- divMod floors (fdiv/fmod); quotRem truncates (tdiv/tmod). Returns a pair.
  | "GHC.Real.divMod"       | "divMod"        =>
      some "(fun a b => (Int.fdiv a b, Int.fmod a b))"
  | "GHC.Real.quotRem"      | "quotRem"       =>
      some "(fun a b => (Int.tdiv a b, Int.tmod a b))"
  -- Lean `Int.gcd`/`Int.lcm` return `Nat`; Haskell returns the numeric type.
  -- Coerce back to `Int` so the emitted term has the Haskell type.
  | "GHC.Real.gcd"          | "gcd"           => some "(fun a b => (Int.gcd a b : Int))"
  | "GHC.Real.lcm"          | "lcm"           => some "(fun a b => (Int.lcm a b : Int))"
  | "GHC.Classes.compare"   | "compare"       => some "compare"
```

- [ ] **Step 4: Implement — `Ordering` type and constructors**

Add to `typeConMap` before `| _, _ => none`:

```lean
  | "Ordering", [] => some "Ordering"
```

Add to `dataConMap` before `| _ => none`:

```lean
  | "LT" | "GHC.Types.LT" => some "Ordering.lt"
  | "EQ" | "GHC.Types.EQ" => some "Ordering.eq"
  | "GT" | "GHC.Types.GT" => some "Ordering.gt"
```

- [ ] **Step 5: Run to verify pass**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat: complete Num/Integral/Ord mappings (fromInteger, signum, divMod, quotRem, gcd/lcm, compare, Ordering)"
```

---

## Task 4: List/Prelude consumers end-to-end (corpus regression)

**Files:**
- Create: `examples/haskell/ListBasics.hs`
- Test: end-to-end build

Locks Tasks 1–3 against the real pipeline and un-breaks the in-flight `OperatorCommons.hs` `listConcat`.

- [ ] **Step 1: Create the fixture**

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module ListBasics where
    import Prelude
    import Lean.Spec (lean)

    listConcat :: [Int] -> [Int] -> [Int]
    listConcat l1 l2 = l1 ++ l2

    doubleAll :: [Int] -> [Int]
    doubleAll = map (\x -> x + x)

    [lean|
    theorem concat_length :
        ∀ (l1 l2 : List Int),
        List.length (listConcat l1 l2) = List.length l1 + List.length l2 := by blaster
    |]
```

- [ ] **Step 2: Transpile and verify**

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/ListBasics.hs && lake build GhcCoreToLean.Generated.ListBasics`
Expected: PASS. `listConcat` emits `List.append l1 l2` (no `GHC.Base._plus__plus_`); `concat_length` reports `✅ Valid`.

- [ ] **Step 3: Re-verify the in-flight example**

Run: `./transpile.sh examples/haskell/OperatorCommons.hs && lake build GhcCoreToLean.Generated.OperatorCommons`
Expected: PASS — `listConcat` now compiles; both theorems verify (or the previously-passing one still does).

- [ ] **Step 4: Build the every-name discovery fixture (catches a wrong LHS loudly)**

The `PreludeNames.hs` from Task 1 Step 0 exercises *every* function mapped in Tasks 1 & 3 (`map filter reverse ++ foldr foldl length null not && || otherwise const flip -`). Re-transpile and build it now that the mappings exist:

Run: `./transpile.sh examples/haskell/PreludeNames.hs && lake build GhcCoreToLean.Generated.PreludeNames`
Expected: PASS — `GhcCoreToLean/Generated/PreludeNames.lean` contains **no** `GHC.*`/`Data.Foldable.*` dangling names. Any remaining dangling name means a mapped LHS is wrong — go back to Task 1/3 and correct it against the Core dump. This is the real verification that Tier 1 works; the `#guard`s alone do not prove it.

- [ ] **Step 5: Commit**

```bash
git add examples/haskell/ListBasics.hs examples/haskell/PreludeNames.hs
git commit -m "test: end-to-end list/Prelude coverage; fixes OperatorCommons.listConcat"
```

---

## Task 5: Partial functions as bottoms (soundness)

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (`isBottomName`, `exprHasBottom`)
- Test: `GhcCoreToLean/Tests/Unit.lean`, end-to-end

⚠️ **Soundness-critical.** Haskell `head []`, `fromJust Nothing`, etc. are ⊥. Routing them to total Lean functions (`List.head!`/`Option.get!`) would let proofs reduce through a defined value where Haskell had ⊥. Instead, extend the **existing** bottom collapse (`error`→`default`, see [memory](../../../.claude/projects/-Users-romainsoulat-ghcCore-to-lean/memory/transpiler-bottoms-and-builtin-ctors.md)) to cover library partials: any application whose spine head is a partial collapses to `default`.

- [ ] **Step 1: Write the failing guards** (the bottom set is private; test via the public emitter)

```lean
-- Task 5: partial library functions collapse to `default` like error/undefined.
-- Build `head xs` and assert the emitted spine collapses to "default".
def headApp : Expr :=
  .app (.var {name := "GHC.List.head", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "xs", unique := 1, ty := .tyCon "List" [.tyVar "a"], role := .id})
#guard emitExpr [] headApp == "default"

def fromJustApp : Expr :=
  .app (.var {name := "Data.Maybe.fromJust", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "m", unique := 1, ty := .tyCon "Maybe" [.tyVar "a"], role := .id})
#guard emitExpr [] fromJustApp == "default"
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL — currently emits an application of a dangling qualified name, not `"default"`.

- [ ] **Step 3: Implement — extend `isBottomName`**

In [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean), add the partials to `isBottomName` (covering bare and qualified forms):

```lean
private def isBottomName : Name → Bool
  | "GHC.Err.error" | "error"
  | "GHC.Err.errorWithoutStackTrace" | "errorWithoutStackTrace"
  | "GHC.Err.undefined" | "undefined"
  -- Partial list functions: ⊥ on the empty list.
  | "GHC.List.head" | "head" | "GHC.List.tail" | "tail"
  | "GHC.List.last" | "last" | "GHC.List.init" | "init"
  | "GHC.List.!!"   | "!!"
  -- Partial Maybe eliminator: ⊥ on Nothing.
  | "Data.Maybe.fromJust" | "fromJust" => true
  | _ => false
```

> `isBottomName` is consulted by both `emitExpr`'s spine-head check and `exprHasBottom` (which triggers the `[Inhabited t]` binder), so this single edit covers emission and the header machinery — no second change needed.

- [ ] **Step 4: Run unit guards**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: End-to-end — confirm a precondition-guarded proof still discharges**

Add `examples/haskell/PartialHead.hs`:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module PartialHead where
    import Prelude
    import Lean.Spec (lean)

    firstOrZero :: [Int] -> Int
    firstOrZero [] = 0
    firstOrZero xs = head xs

    [lean|
    theorem firstOrZero_nonneg :
        ∀ (xs : List Int), (∀ x, List.elem x xs → x ≥ 0) → firstOrZero xs ≥ 0 := by blaster
    |]
```

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/PartialHead.hs && lake build GhcCoreToLean.Generated.PartialHead`
Expected: PASS — `head xs` in the non-empty branch emits `default`; the `[]` branch returns `0`. (If `blaster` cannot discharge through `default` here, that is expected per the README's bottom note — record the outcome; the soundness property is that it does **not** falsely prove a `head []`-dependent claim.)

- [ ] **Step 6: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/PartialHead.hs
git commit -m "fix(soundness): route partial functions (head/tail/!!/fromJust) through the bottom path, not total Lean fns"
```

---

## Task 6: Bind the case binder (soundness)

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (`emitExpr` `.case_` arm; `occursInExpr` reused)
- Test: `GhcCoreToLean/Tests/Unit.lean`, end-to-end

GHC `case e of cb { … }` binds `cb` to the scrutinee value; alts may reference `cb`. [Parse.lean:137](../../../GhcCoreToLean/Parse.lean#L137) captures `cb` but [Emit.lean](../../../GhcCoreToLean/Emit.lean) discards it (`.case_ scr _cb _ty alts`), so any alt referencing it emits an unbound local — a silent miscompile. Fix: when `cb` occurs in any alt RHS, wrap the match in `let <cb> := <scrutinee>`.

- [ ] **Step 1: Write the failing guard**

```lean
-- Task 6: a case binder referenced in an alt must be bound via `let`.
def caseWithBinder : Expr :=
  let cb : Var := {name := "wild", unique := 7, ty := .tyCon "Int" [], role := .id}
  .case_
    (.var {name := "n", unique := 1, ty := .tyCon "Int" [], role := .id})
    cb (.tyCon "Int" [])
    [ .mk (.litAlt (.litInt 0)) [] (.lit (.litInt 0)),
      .mk .default [] (.var cb) ]   -- DEFAULT references the case binder
#guard (emitExpr [] caseWithBinder).splitOn "let wild_7 :=" |>.length == 2
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL — emitted text has no `let wild_7 :=`; instead a bare `wild_7` (unbound) appears.

- [ ] **Step 3: Implement — bind the case binder when used**

In [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean), replace the `.case_` arm of `emitExpr`:

```lean
    | .case_ scr cb _ty alts =>
      let alts'   := reorderAlts alts
      let altsStr := alts'.map (emitAlt top)
      let scrStr  := emitExpr top scr
      let body    := String.intercalate "\n" altsStr
      -- GHC binds the case binder to the scrutinee; alts may reference it.
      -- When used, bind it once and match *on the binder* — single evaluation
      -- of the scrutinee, matching Core's semantics (alts scrutinize the bound
      -- value). When unused, match the scrutinee directly.
      let usesCb  := alts.any (fun (.mk _ _ r) => occursInExpr cb.name r)
      if usesCb then
        s!"(let {localId cb} := {scrStr}\n(match {localId cb} with\n{body}))"
      else
        s!"(match {scrStr} with\n{body})"
```

> `occursInExpr` is already defined above `emitExpr` in the same file and takes `(Name) (Expr)`. Reusing it keeps the "only bind when used" optimization, avoiding spurious `let`s and unused-variable lints.

- [ ] **Step 4: Run unit guard**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: End-to-end — a strict nested match that uses the binder**

Add `examples/haskell/CaseBinder.hs`:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module CaseBinder where
    import Prelude

    -- `n` is reused on the RHS; the desugarer often binds the scrutinee
    -- to the case binder and references it, exercising the fix.
    clampPos :: Int -> Int
    clampPos n = case n of
        0 -> 0
        _ -> if n < 0 then 0 else n
```

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/CaseBinder.hs && lake build GhcCoreToLean.Generated.CaseBinder`
Expected: PASS — no unbound identifier error in `GhcCoreToLean/Generated/CaseBinder.lean`.

- [ ] **Step 6: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/CaseBinder.hs
git commit -m "fix(soundness): bind the GHC case binder via let when referenced in alts"
```

---

## Task 7: Local recursive `let` (`let rec`)

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (`emitLet` `.rec_` arm)
- Test: `GhcCoreToLean/Tests/Unit.lean`, end-to-end

Today `emitLet (.rec_ …)` emits a `-- TODO … unsupported` comment and broken bindings. Lean expresses local recursion with `let rec`. Single-binding rec is the common case; multi-binding becomes a sequence of `let rec`.

- [ ] **Step 1: Write the failing guard**

```lean
-- Task 7: local recursive let emits `let rec`, not a TODO comment.
def localRecLet : Bind :=
  .rec_ [ ( {name := "go", unique := 3, ty := .tyFun (.tyCon "Int" []) (.tyCon "Int" []), role := .id},
            .lam {name := "k", unique := 4, ty := .tyCon "Int" [], role := .id}
                 (.var {name := "k", unique := 4, ty := .tyCon "Int" [], role := .id}) ) ]
#guard (emitLet [] localRecLet).splitOn "let rec go_3" |>.length == 2
#guard (emitLet [] localRecLet).splitOn "TODO" |>.length == 1   -- no TODO marker
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL — current output contains `TODO` and no `let rec`.

- [ ] **Step 3: Implement — `emitLet` `.rec_` arm**

In [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean), replace the `.rec_` arm of `emitLet`. Each binding's lambdas are peeled into parameters so the `let rec` reads naturally; the body is emitted recursively.

```lean
  | .rec_ pairs =>
    -- Local recursion → `let rec`. Each binding peels its lambdas into
    -- parameters; multiple bindings emit as consecutive `let rec` lines
    -- (Lean allows mutually-referencing `let rec` blocks via `and`, but the
    -- desugarer almost always produces a single self-recursive join binding).
    let lines := pairs.map fun (v, e) =>
      let rec peel : Expr → List Var × Expr
        | .lam bv body => let (vs, b) := peel body; (bv :: vs, b)
        | other        => ([], other)
      let (params, body) := peel e
      let paramStr := String.intercalate " " (params.map (fun p => s!"({localId p})"))
      let head := if paramStr.isEmpty then s!"let rec {localId v} :="
                  else s!"let rec {localId v} {paramStr} :="
      s!"{head} {emitExpr top body}"
    String.intercalate "\n" lines
```

> **Termination is the hard edge, and it is the common case, not the exception.** `let rec` has **no** `decreasing_by` hook (unlike the top-level defs, which the codebase already escapes with `decreasing_by all_goals sorry`). So a local rec that is *not* structurally decreasing — e.g. counting down on `Int` — will fail to elaborate as `let rec`. **Therefore the structural case (recursion on a `List`/inductive argument) is the only one `let rec` handles directly; for non-structural local recursion the executor must lift the binding to a top-level `def` and reuse the existing `decreasing_by all_goals sorry` machinery in `emitBind`.** Implement the structural `let rec` path here; if the Step-5 fixture or a real example hits non-structural recursion, that lift is a follow-up task (note it, don't fake termination).

- [ ] **Step 4: Run unit guards**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: End-to-end fixture**

Add `examples/haskell/LocalRec.hs` — **structural** recursion on a list, so `let rec` elaborates without a termination hook:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module LocalRec where
    import Prelude

    -- `go` recurses on the list spine (structurally decreasing), which Lean's
    -- `let rec` accepts directly. (Int countdown recursion would need the
    -- top-level lift described in Step 3 and is out of scope for this task.)
    sumList :: [Int] -> Int
    sumList xs = go xs 0
      where
        go []     acc = acc
        go (y:ys) acc = go ys (acc + y)
```

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/LocalRec.hs && lake build GhcCoreToLean.Generated.LocalRec`
Expected: PASS — `go` emits as a `let rec` and elaborates (structural recursion on `ys`).

- [ ] **Step 6: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/LocalRec.hs
git commit -m "feat: emit local recursive let as `let rec` (was an unsupported TODO)"
```

---

## Task 8: Arithmetic/comparison primops (`valueMap`)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean` (`valueMap`)
- Test: `GhcCoreToLean/Tests/Unit.lean`

The README notes optimizer passes introduce unboxed primops the lowering doesn't handle; even pass-0000 leaks some (`+#`, `==#`, …). Map the common arithmetic/comparison ones to their boxed Lean equivalents. ⚠️ Comparison primops return unboxed `Int#` (0/1), but at the boxed level Haskell wraps them to `Bool`; map `==#` etc. to the same `decide`-wrapped forms already used for `GHC.Classes.*` so the result type is `Bool`.

- [ ] **Step 1: Write the failing guards**

```lean
-- Task 8: unboxed arithmetic/comparison primops.
#guard valueMap "GHC.Prim.+#"  == some "(· + ·)"
#guard valueMap "GHC.Prim.-#"  == some "(· - ·)"
#guard valueMap "GHC.Prim.*#"  == some "(· * ·)"
#guard valueMap "GHC.Prim.==#" == some "(· == ·)"
#guard valueMap "GHC.Prim.<#"  == some "(fun a b => decide (a < b))"
#guard valueMap "GHC.Prim.<=#" == some "(fun a b => decide (a ≤ b))"
#guard valueMap "GHC.Prim.>#"  == some "(fun a b => decide (a > b))"
#guard valueMap "GHC.Prim.>=#" == some "(fun a b => decide (a ≥ b))"
#guard valueMap "GHC.Prim./=#" == some "(fun a b => !(a == b))"
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL on the new guards.

- [ ] **Step 3: Implement — `valueMap` primop arms**

Add before `| _ => none`:

```lean
  -- Unboxed Int# primops. Arithmetic maps to boxed ops (I#/Int# both → Int);
  -- comparisons mirror the GHC.Classes.* `decide`-wrapped Bool forms.
  | "GHC.Prim.+#"  => some "(· + ·)"
  | "GHC.Prim.-#"  => some "(· - ·)"
  | "GHC.Prim.*#"  => some "(· * ·)"
  | "GHC.Prim.==#" => some "(· == ·)"
  | "GHC.Prim./=#" => some "(fun a b => !(a == b))"
  | "GHC.Prim.<#"  => some "(fun a b => decide (a < b))"
  | "GHC.Prim.<=#" => some "(fun a b => decide (a ≤ b))"
  | "GHC.Prim.>#"  => some "(fun a b => decide (a > b))"
  | "GHC.Prim.>=#" => some "(fun a b => decide (a ≥ b))"
```

- [ ] **Step 4: Run to verify pass**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat: map unboxed Int# arithmetic/comparison primops"
```

---

## Task 9: Maybe / Either eliminators (`valueMap`)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean` (`valueMap`)
- Test: `GhcCoreToLean/Tests/Unit.lean`

Total eliminators (the ctors/types are already mapped in `typeConMap`/`dataConMap`). `fromJust` is partial → already a bottom (Task 5), not here.

- [ ] **Step 1: Write the failing guards**

```lean
-- Task 9: total Maybe/Either eliminators.
#guard valueMap "GHC.Maybe.maybe"     == some "(fun d f m => Option.elim m d f)"
#guard valueMap "Data.Maybe.fromMaybe"== some "(fun d m => Option.getD m d)"
#guard valueMap "Data.Maybe.isJust"   == some "Option.isSome"
#guard valueMap "Data.Maybe.isNothing"== some "Option.isNone"
#guard valueMap "Data.Either.either"  == some "(fun f g e => Sum.elim e f g)"
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL on new guards.

- [ ] **Step 3: Implement — `valueMap` arms**

Add before `| _ => none`:

```lean
  -- Maybe/Either eliminators. `maybe d f Nothing = d`, `maybe d f (Just x) = f x`
  -- matches `Option.elim m d f`. `either f g` matches `Sum.elim e f g`.
  | "GHC.Maybe.maybe"      | "maybe"     => some "(fun d f m => Option.elim m d f)"
  | "Data.Maybe.fromMaybe" | "fromMaybe" => some "(fun d m => Option.getD m d)"
  | "Data.Maybe.isJust"    | "isJust"    => some "Option.isSome"
  | "Data.Maybe.isNothing" | "isNothing" => some "Option.isNone"
  | "Data.Either.either"   | "either"    => some "(fun f g e => Sum.elim e f g)"
```

> Verify `Option.elim`'s argument order against the Lean 4 `v4.24.0` stdlib during Step 4 (it is `Option.elim (o : Option α) (default : β) (f : α → β)`). If the order differs in the pinned toolchain, adjust the lambda — this is the silent-wrong risk for this task.

- [ ] **Step 4: Run to verify pass**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat: map total Maybe/Either eliminators (maybe, fromMaybe, isJust, either)"
```

---

## Task 10: Documentation — update README coverage & limitations

**Files:**
- Modify: `README.md`

- [ ] **Step 1: Update the Limitations section**

In [README.md](../../../README.md), under *Limitations*, replace the bullet "later optimizer passes introduce primops the lowering doesn't handle" with the current state:

```markdown
- The pipeline consumes the `pass-0000` (desugarer) Core. Common unboxed
  `Int#` primops are mapped; exotic primops (string/array/IO) are not.
- Mapped `base` surface: arithmetic (`+ - * negate abs signum`),
  integral (`quot rem div mod divMod quotRem gcd lcm fromIntegral`),
  comparison/`Ord` (`== /= < <= > >= min max compare`/`Ordering`),
  booleans (`&& || not otherwise`), combinators (`id . const flip $ seq`),
  the total list library (`++ map filter foldr foldl length reverse null`),
  tuples, and `Maybe`/`Either` eliminators.
- Partial functions (`error`, `undefined`, `head`, `tail`, `init`, `last`,
  `!!`, `fromJust`) lower to Lean `default` (a total, sound bottom); proofs
  that reduce through them stay sound, so properties should carry the
  preconditions that rule the partial branch out.
- Not yet supported: user-defined type classes / dictionary passing (only
  derived `Eq`→`BEq` is wired), `Show`/`Read`, and the `Functor`/`Monad`
  hierarchy. See the typeclasses plan.
```

- [ ] **Step 2: Commit**

```bash
git add README.md
git commit -m "docs: document expanded base-library and primop coverage"
```

---

## Self-Review Notes

- **Spec coverage:** Tier 1a (list/Prelude) → Tasks 1, 4; Tier 1b (tuples) → Task 2; Tier 1c (Num/Integral/Ord) → Task 3; partials-as-bottoms → Task 5; case binder → Task 6; local `let rec` → Task 7; primops → Task 8; Maybe/Either → Task 9. Tier 3 (typeclasses) is the separate plan. ✅
- **Type consistency:** all guards call `valueMap`/`typeConMap`/`dataConMap`/`emitExpr`/`emitLet`/`emitAltPattern` with the signatures in the current source; `Var` literals use the real field set (`name unique ty role`). ✅
- **Open risks flagged inline (not placeholders):** exact GHC tuple ctor name (Task 2 Step 2 discovery), `Option.elim` arg order (Task 9), local-rec termination edge (Task 7). Each has a concrete fallback.
