# M1 — Lists & Tuples Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make list literals (`[1,2,3]`), Int ranges (`[a..b]`, `[a,b..c]`), 3-/4-tuple construction, and the missing total list library (`take`/`drop`/`zip`/`sum`/`elem`/…) transpile and verify end-to-end, per the approved spec [2026-07-24-coverage-roadmap-design.md](../specs/2026-07-24-coverage-roadmap-design.md) §M1.

**Architecture:** Three classes of change, same as the Tiers-1-2 milestone. (1) **Mapping-table additions** in [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean) — pure functions, unit-tested with `#guard` in [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean). (2) A new **runtime support module** [GhcCoreToLean/Runtime.lean](../../../GhcCoreToLean/Runtime.lean) (namespace `Hs`) holding named helpers too complex for inline lambdas; generated files import it (one-line header change in [Main.lean](../../../Main.lean)). (3) One small **Emit** change (4-tuple patterns). Every feature lands with an end-to-end fixture in `examples/haskell/` whose properties build `✅ Valid`.

**Tech Stack:** Lean 4 (`v4.24.0`), `lake`; GHC 9.2.7 + cabal via `./transpile.sh`; Blaster for property verification.

**Branch:** `feature/m1-lists-tuples` off `main`.

---

## Soundness discipline (read first)

This is a *prover*, not just a compiler. Two failure modes:

- **Loud-fail (safe):** a dangling Lean name that won't compile — the user sees it.
- **Silent-wrong (unsound):** compiles but encodes different semantics, so `by blaster` proves a theorem about the wrong function. **Never acceptable.**

Rules for this milestone:

- Negative-count clamping: Haskell `take (-1) xs = []`; `Int.toNat` clamps negatives to 0 — semantics **match**, which is why `List.take n.toNat xs` is faithful, not a shortcut.
- `maximum`/`minimum` are **partial** (⊥ on `[]`): they route through the `default` bottom path like `head`, and must be registered in `Emit.isPartialDefaultName`.
- Infinite producers (`iterate`, `repeat`, `cycle`, `enumFrom`, `enumFromThen`) stay **unmapped** — loud compile failure.
- Every mapping uses either dot-notation (`xs.contains x`) or an eta-wrap that pins Haskell argument order explicitly, plus a **semantic-pin `#guard`** that evaluates the Lean target on concrete input, so a Lean-side signature surprise breaks the build instead of flipping argument order silently.

## Name-observation rule (applies to every mapping task)

GHC's desugarer emits *qualified* names that vary per function (`GHC.List.take` vs `Data.Foldable.sum` vs `GHC.Base.build`). The keys written in this plan are the expected ones, with both plausible qualifications hedged. **Each fixture task transpiles FIRST and greps the generated file** for the actual name; if it differs from the plan's key, add the observed name as an extra alternative on the same arm (never replace the hedges — extra keys are harmless, missing keys are loud-fail). Record observed names in a comment above the `#guard`s, as `Tests/Unit.lean` already does for tuples/NumOrd.

## Per-task dev loop

1. Edit.
2. `lake build GhcCoreToLean` — runs every `#guard`.
3. For end-to-end steps: `lake build ghccoretolean` (the *binary* must be rebuilt before transpiling — stale-binary output is the classic trap), then `./transpile.sh examples/haskell/<Module>.hs`, then `lake build GhcCoreToLean.Generated.<Module>` and look for `✅ Valid` on each property.

Property tactics in fixtures: `by blaster` for quantified linear-arithmetic goals (see `MaxMinOverArithmetics.hs`); `by decide` for concrete-value goals; `by rfl` where definitional. If `decide` times out on a concrete goal, switch that property to `native_decide`. If `blaster` cannot discharge a tuple/list goal, replace with the tactic noted in that task.

---

## File Structure

- **Create** [GhcCoreToLean/Runtime.lean](../../../GhcCoreToLean/Runtime.lean) — namespace `Hs`: `enumFromTo`, `enumFromThenTo`, `splitAt`, `and`, `or`.
- **Modify** [GhcCoreToLean.lean](../../../GhcCoreToLean.lean) — `import GhcCoreToLean.Runtime`.
- **Modify** [Main.lean](../../../Main.lean) (~line 136) — generated-file header gains `import GhcCoreToLean.Runtime`.
- **Modify** [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean) — `valueMap`, `typeConMap`, `dataConMap` additions.
- **Modify** [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — `emitAltPattern` 4-tuple arm (~line 162); `isPartialDefaultName` (+`maximum`/`minimum`, ~line 196).
- **Modify** [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean) — `#guard` sections per task.
- **Create** `examples/haskell/TupleTriple.hs`, `examples/haskell/ListLiterals.hs`, `examples/haskell/ListLibrary.hs` — fixtures (ListLiterals/ListLibrary grow across tasks).
- **Modify** [README.md](../../../README.md) — Limitations section (final task).

---

### Task 1: Runtime support module + generated-header wiring

**Files:**
- Create: `GhcCoreToLean/Runtime.lean`
- Modify: `GhcCoreToLean.lean`
- Modify: `Main.lean` (header assembly, ~line 136)

- [ ] **Step 1: Create the module (empty namespace for now — helpers arrive with the tasks that need them)**

```lean
/-! # Haskell runtime support helpers

Named Lean images for `base` functions whose faithful translation is too
complex for a readable inline lambda in `Maps.lean` (spec: 2026-07-24
coverage-roadmap §"runtime support module"). Generated files import this
module unconditionally; helpers are ordinary defs, `#guard`-tested in
`Tests/Unit.lean`, and stable named symbols for Blaster to unfold. -/

namespace Hs

end Hs
```

- [ ] **Step 2: Wire it into the library root**

In `GhcCoreToLean.lean`, add alongside the existing imports:

```lean
import GhcCoreToLean.Runtime
```

- [ ] **Step 3: Emit the import in every generated file**

In `Main.lean` (~line 136), change:

```lean
    let header     := s!"import Lean\nimport Blaster\n{depImports}\n"
```

to:

```lean
    let header     := s!"import Lean\nimport Blaster\nimport GhcCoreToLean.Runtime\n{depImports}\n"
```

- [ ] **Step 4: Build + end-to-end regression (proves the new import resolves in generated files)**

```bash
lake build GhcCoreToLean && lake build ghccoretolean
./transpile.sh examples/haskell/Ratio.hs
lake build GhcCoreToLean.Generated.Ratio
```

Expected: builds succeed; `Generated/Ratio.lean` starts with the three imports; properties still `✅ Valid`.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Runtime.lean GhcCoreToLean.lean Main.lean
git commit -m "feat(runtime): add Hs runtime-support module, imported by generated files"
```

---

### Task 2: 3-/4-tuple construction and 4-tuple type/patterns

**Files:**
- Modify: `GhcCoreToLean/Maps.lean` (`dataConMap` ~line 169, `typeConMap` ~line 154)
- Modify: `GhcCoreToLean/Emit.lean` (`emitAltPattern` ~line 162)
- Modify: `GhcCoreToLean/Tests/Unit.lean`
- Create: `examples/haskell/TupleTriple.hs`

- [ ] **Step 1: Write failing `#guard`s in `Tests/Unit.lean`**

```lean
-- M1 Task 2: 3-/4-tuple construction. Ctors are eta-expanded lambdas so plain
-- left-application works at any saturation.
#guard dataConMap "(,,)"            == some "(fun a b c => (a, b, c))"
#guard dataConMap "GHC.Tuple.(,,)"  == some "(fun a b c => (a, b, c))"
#guard dataConMap "(,,,)"           == some "(fun a b c d => (a, b, c, d))"
#guard dataConMap "GHC.Tuple.(,,,)" == some "(fun a b c d => (a, b, c, d))"
#guard typeConMap "(,,,)" ["Int", "Int", "Int", "Int"] == some "(Int × Int × Int × Int)"
#guard typeConMap "GHC.Tuple.(,,,)" ["Int", "Int", "Int", "Int"] == some "(Int × Int × Int × Int)"
#guard emitAltPattern (.dataCon "(,,,)")
         [ {name := "a", unique := 1, ty := .tyCon "Int" [], role := .id},
           {name := "b", unique := 2, ty := .tyCon "Int" [], role := .id},
           {name := "c", unique := 3, ty := .tyCon "Int" [], role := .id},
           {name := "d", unique := 4, ty := .tyCon "Int" [], role := .id} ]
       == "(a_1, b_2, c_3, d_4)"
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL — `#guard` evaluated to false (dataConMap returns `none`).

- [ ] **Step 3: Implement**

In `Maps.lean` `dataConMap`, replace the `NOTE: 3-tuple construction is intentionally NOT mapped` comment block (above the `(,)` arm) and add after the `(,)` arm:

```lean
  -- 3-/4-tuple construction. Eta-expanded lambdas, NOT `Prod.mk` (which is
  -- binary — left-applying it to 3 args is ill-typed): `(fun a b c => (a,b,c))`
  -- left-applies correctly at any saturation. 5+-tuples remain unmapped (loud).
  | "(,,)"  | "GHC.Tuple.(,,)"  => some "(fun a b c => (a, b, c))"
  | "(,,,)" | "GHC.Tuple.(,,,)" => some "(fun a b c d => (a, b, c, d))"
```

In `typeConMap`, after the `(,,)` arms:

```lean
  | "(,,,)", [a, b, c, d]           => some s!"({a} × {b} × {c} × {d})"
  | "GHC.Tuple.(,,,)", [a, b, c, d] => some s!"({a} × {b} × {c} × {d})"
```

In `Emit.lean` `emitAltPattern` (~line 162), extend the tuple-name condition:

```lean
    if name == "(,)" || name == "(,,)" || name == "(,,,)"
       || name == "GHC.Tuple.(,)" || name == "GHC.Tuple.(,,)"
       || name == "GHC.Tuple.(,,,)" then
```

- [ ] **Step 4: Run to verify pass**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: Create the fixture `examples/haskell/TupleTriple.hs`**

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module TupleTriple where

triple :: Int -> Int -> Int -> (Int, Int, Int)
triple a b c = (a, b, c)

sumTriple :: (Int, Int, Int) -> Int
sumTriple (a, b, c) = a + b + c

rotate :: (Int, Int, Int) -> (Int, Int, Int)
rotate (a, b, c) = (b, c, a)

quad :: Int -> Int -> Int -> Int -> (Int, Int, Int, Int)
quad a b c d = (a, b, c, d)

fourth :: (Int, Int, Int, Int) -> Int
fourth (_, _, _, d) = d

{- @lean
theorem sumTriple_triple :
    ∀ (a b c : Int), sumTriple (triple a b c) = a + b + c := by blaster
-}

{- @lean
theorem rotate_sum :
    ∀ (a b c : Int), sumTriple (rotate (triple a b c)) = a + b + c := by blaster
-}

{- @lean
theorem fourth_quad :
    ∀ (a b c d : Int), fourth (quad a b c d) = d := by blaster
-}
```

- [ ] **Step 6: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/TupleTriple.hs
lake build GhcCoreToLean.Generated.TupleTriple
```

Expected: 3 × `✅ Valid`. Per the name-observation rule, if the generated file
shows a ctor name other than `(,,)`/`GHC.Tuple.(,,)` in value position, add the
observed key to the same `dataConMap` arm. If `blaster` cannot discharge these
tuple goals, replace each tactic with `by intro a b c; rfl` (resp.
`intro a b c d`) — the compositions reduce definitionally — and note it in the
fixture.

- [ ] **Step 7: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/TupleTriple.hs
git commit -m "feat(tuples): 3-/4-tuple construction, 4-tuple type + patterns"
```

---

### Task 3: List literals (`build`/`augment`)

**Files:**
- Create: `examples/haskell/ListLiterals.hs`
- Modify: `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`

- [ ] **Step 1: Create the fixture FIRST (name observation)**

`examples/haskell/ListLiterals.hs`:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module ListLiterals where

smallList :: [Int]
smallList = [1, 2, 3]

withPrefix :: [Int] -> [Int]
withPrefix xs = [1, 2] ++ xs

{- @lean
theorem smallList_val : smallList = [1, 2, 3] := by rfl
-}

{- @lean
theorem withPrefix_example : withPrefix [7] = [1, 2, 7] := by decide
-}
```

- [ ] **Step 2: Transpile and observe the desugared names**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLiterals.hs
grep -n "build\|augment" GhcCoreToLean/Generated/ListLiterals.lean
```

Expected: the generated file references `GHC.Base.build` (and, for
`withPrefix`, either `GHC.Base.augment` or plain `++` over an inner `build`).
`lake build GhcCoreToLean.Generated.ListLiterals` at this point FAILS loudly
(unknown identifier) — that failure is the "failing test" for this task.

- [ ] **Step 3: Write failing `#guard`s**

```lean
-- M1 Task 3: list literals. `[a,b,c]` desugars to `build (\c n -> c a (c b (c c n)))`
-- with `build g = g (:) []`; `augment g xs = g (:) xs` (literal ++ xs fusion form).
-- Type args/binders on `g` are already erased by Lower; emitted lambdas carry
-- no binder type annotations, so the rank-2 type cannot dangle.
#guard valueMap "GHC.Base.build"   == some "(fun g => g List.cons List.nil)"
#guard valueMap "GHC.Base.augment" == some "(fun g xs => g List.cons xs)"
```

Run: `lake build GhcCoreToLean` — expected FAIL.

- [ ] **Step 4: Implement in `Maps.lean` `valueMap`** (after the `GHC.Base.++` arm)

```lean
  -- List literals. `[a,b,c]` desugars to `GHC.Base.build (\c n -> c a (c b (c c n)))`
  -- where `build g = g (:) []`; `augment g xs = g (:) xs` appears for
  -- `[literal] ++ xs` fusion forms. Lower erases the rank-2 type application.
  | "GHC.Base.build"   => some "(fun g => g List.cons List.nil)"
  | "GHC.Base.augment" => some "(fun g xs => g List.cons xs)"
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 5: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLiterals.hs
lake build GhcCoreToLean.Generated.ListLiterals
```

Expected: builds; both properties `✅ Valid` (the `rfl` one closes by
beta-reduction of the emitted `build` application; the `decide` one evaluates
through `augment`/`append`).

- [ ] **Step 6: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLiterals.hs
git commit -m "feat(lists): list-literal syntax via build/augment mapping"
```

---

### Task 4: Int ranges (`enumFromTo`, `enumFromThenTo`)

**Files:**
- Modify: `GhcCoreToLean/Runtime.lean`, `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/ListLiterals.hs`

- [ ] **Step 1: Write failing semantic `#guard`s in `Tests/Unit.lean`**

```lean
-- M1 Task 4: Int ranges. Semantics pinned against GHC:
--   [1..5]=[1,2,3,4,5]  [3..3]=[3]  [3..1]=[]
--   [1,3..9]=[1,3,5,7,9]  [1,3..8]=[1,3,5,7]  [10,8..5]=[10,8,6]
--   [5,7..4]=[]  [5,3..6]=[]  [1,1..0]=[]  ([1,1..5] is infinite ⇒ default=[])
#guard Hs.enumFromTo 1 5 == [1, 2, 3, 4, 5]
#guard Hs.enumFromTo 3 3 == [3]
#guard Hs.enumFromTo 3 1 == []
#guard Hs.enumFromTo (-2) 1 == [-2, -1, 0, 1]
#guard Hs.enumFromThenTo 1 3 9 == [1, 3, 5, 7, 9]
#guard Hs.enumFromThenTo 1 3 8 == [1, 3, 5, 7]
#guard Hs.enumFromThenTo 10 8 5 == [10, 8, 6]
#guard Hs.enumFromThenTo 5 7 4 == []
#guard Hs.enumFromThenTo 5 3 6 == []
#guard Hs.enumFromThenTo 1 1 0 == []
```

(Also add `import GhcCoreToLean.Runtime` to `Tests/Unit.lean`'s imports.)

Run: `lake build GhcCoreToLean` — expected FAIL (`unknown constant Hs.enumFromTo`).

- [ ] **Step 2: Implement in `Runtime.lean`** (inside `namespace Hs`)

```lean
/-- Haskell `[lo .. hi]` (`GHC.Enum.enumFromTo` at `Int`). Empty when `hi < lo`. -/
def enumFromTo (lo hi : Int) : List Int :=
  (List.range (hi + 1 - lo).toNat).map (fun i => lo + i)

/-- Haskell `[a, b .. c]` (`GHC.Enum.enumFromThenTo` at `Int`), stride `b - a`.
    Faithful on every finite case (positive stride, negative stride, and the
    zero-stride `c < a` case, which GHC makes `[]`). The zero-stride `c ≥ a`
    case is an *infinite* list in Haskell — every total observation of it is
    ⊥ — so it lowers to `default` (= `[]`), the project's sound-bottom
    convention. -/
def enumFromThenTo (a b c : Int) : List Int :=
  let d := b - a
  if d > 0 then
    if a > c then []
    else (List.range ((c - a).toNat / d.toNat + 1)).map (fun i => a + d * i)
  else if d < 0 then
    if a < c then []
    else (List.range ((a - c).toNat / (-d).toNat + 1)).map (fun i => a + d * i)
  else
    default
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 3: Write failing mapping `#guard`s, then implement**

```lean
#guard valueMap "GHC.Enum.enumFromTo"     == some "Hs.enumFromTo"
#guard valueMap "GHC.Enum.enumFromThenTo" == some "Hs.enumFromThenTo"
```

In `Maps.lean` `valueMap` (next to the literal mappings from Task 3):

```lean
  -- Int ranges (Enum dict is erased by Lower). `enumFrom`/`enumFromThen`
  -- (infinite) are intentionally NOT mapped — loud fail.
  | "GHC.Enum.enumFromTo"     => some "Hs.enumFromTo"
  | "GHC.Enum.enumFromThenTo" => some "Hs.enumFromThenTo"
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 4: Extend the fixture and go end-to-end**

Append to `examples/haskell/ListLiterals.hs`:

```haskell
rangeList :: [Int]
rangeList = [1 .. 5]

countdown :: [Int]
countdown = [10, 8 .. 5]

{- @lean
theorem rangeList_val : rangeList = [1, 2, 3, 4, 5] := by decide
-}

{- @lean
theorem countdown_val : countdown = [10, 8, 6] := by decide
-}
```

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLiterals.hs
lake build GhcCoreToLean.Generated.ListLiterals
```

Expected: all 4 properties `✅ Valid`. Observe the actual Core name via
`grep -n "enumFrom" GhcCoreToLean/Generated/ListLiterals.lean` before the
mapping lands (per the name-observation rule).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Runtime.lean GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLiterals.hs
git commit -m "feat(lists): Int ranges enumFromTo/enumFromThenTo via Hs runtime helpers"
```

---

### Task 5: Int-indexed list ops (`take`, `drop`, `splitAt`, `replicate`)

**Files:**
- Modify: `GhcCoreToLean/Runtime.lean`, `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`
- Create: `examples/haskell/ListLibrary.hs`

- [ ] **Step 1: Failing `#guard`s**

```lean
-- M1 Task 5: Int-indexed ops. Haskell take/drop/replicate/splitAt treat a
-- negative count as 0; Int.toNat clamps negatives to 0 — semantics MATCH.
#guard Hs.splitAt 1 [5, 6, 7] == ([5], [6, 7])
#guard Hs.splitAt (-2) [1] == ([], [1])
#guard Hs.splitAt 9 [1] == ([1], [])
#guard valueMap "GHC.List.take"      == some "(fun n xs => List.take n.toNat xs)"
#guard valueMap "GHC.List.drop"      == some "(fun n xs => List.drop n.toNat xs)"
#guard valueMap "GHC.List.splitAt"   == some "Hs.splitAt"
#guard valueMap "GHC.List.replicate" == some "(fun n x => List.replicate n.toNat x)"
```

Run: `lake build GhcCoreToLean` — expected FAIL.

- [ ] **Step 2: Implement**

`Runtime.lean` (inside `namespace Hs`):

```lean
/-- Haskell `splitAt n xs = (take n xs, drop n xs)`; negative `n` acts as 0
    (`Int.toNat` clamps, matching GHC). -/
def splitAt (n : Int) (xs : List α) : List α × List α :=
  (xs.take n.toNat, xs.drop n.toNat)
```

`Maps.lean` `valueMap`:

```lean
  -- Int-indexed list ops. Haskell clamps negative counts to "empty/unchanged";
  -- `Int.toNat` clamps negatives to 0 — the semantics match exactly.
  | "GHC.List.take"      => some "(fun n xs => List.take n.toNat xs)"
  | "GHC.List.drop"      => some "(fun n xs => List.drop n.toNat xs)"
  | "GHC.List.splitAt"   => some "Hs.splitAt"
  | "GHC.List.replicate" => some "(fun n x => List.replicate n.toNat x)"
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 3: Create the fixture `examples/haskell/ListLibrary.hs`** (grown by Tasks 6-9)

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module ListLibrary where

takeSome :: Int -> [Int] -> [Int]
takeSome n xs = take n xs

dropSome :: Int -> [Int] -> [Int]
dropSome n xs = drop n xs

splitSome :: Int -> [Int] -> ([Int], [Int])
splitSome n xs = splitAt n xs

fill :: Int -> Int -> [Int]
fill n x = replicate n x

{- @lean
theorem takeSome_example : takeSome 2 [1, 2, 3] = [1, 2] := by decide
-}

{- @lean
theorem takeSome_neg : takeSome (-1) [1, 2, 3] = [] := by decide
-}

{- @lean
theorem splitSome_example : splitSome 1 [5, 6, 7] = ([5], [6, 7]) := by decide
-}

{- @lean
theorem fill_example : fill 3 9 = [9, 9, 9] := by decide
-}
```

- [ ] **Step 4: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLibrary.hs
lake build GhcCoreToLean.Generated.ListLibrary
```

Expected: 4 × `✅ Valid`. Observe names first:
`grep -n "take\|drop\|splitAt\|replicate" GhcCoreToLean/Generated/ListLibrary.lean`.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Runtime.lean GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLibrary.hs
git commit -m "feat(lists): take/drop/splitAt/replicate with faithful negative-count clamping"
```

---

### Task 6: Zip family (`zip`, `zipWith`, `unzip`)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/ListLibrary.hs`

- [ ] **Step 1: Failing `#guard`s (mapping + semantic pins for Lean signatures)**

```lean
-- M1 Task 6: zip family. Semantic pins: if a Lean signature ever flips
-- argument order, these evaluation guards break the build.
#guard List.zipWith (· + ·) [1, 2] [10, 20] == [11, 22]
#guard List.zip [1, 2] [10, 20, 30] == [(1, 10), (2, 20)]
#guard List.unzip [(1, 10), (2, 20)] == ([1, 2], [10, 20])
#guard valueMap "GHC.List.zip"     == some "(fun xs ys => List.zip xs ys)"
#guard valueMap "GHC.List.zipWith" == some "(fun f xs ys => List.zipWith f xs ys)"
#guard valueMap "GHC.List.unzip"   == some "List.unzip"
```

Run: `lake build GhcCoreToLean` — expected FAIL on the `valueMap` guards.

- [ ] **Step 2: Implement in `Maps.lean` `valueMap`**

```lean
  -- Zip family. Eta-wrapped to pin Haskell arg order (f, xs, ys).
  | "GHC.List.zip"                        => some "(fun xs ys => List.zip xs ys)"
  | "GHC.List.zipWith"                    => some "(fun f xs ys => List.zipWith f xs ys)"
  | "GHC.List.unzip" | "Data.List.unzip"  => some "List.unzip"
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 3: Extend the fixture**

Append to `examples/haskell/ListLibrary.hs`:

```haskell
pairUp :: [Int] -> [Int] -> [(Int, Int)]
pairUp xs ys = zip xs ys

addWise :: [Int] -> [Int] -> [Int]
addWise xs ys = zipWith (+) xs ys

split2 :: [(Int, Int)] -> ([Int], [Int])
split2 ps = unzip ps

{- @lean
theorem pairUp_example : pairUp [1, 2] [3, 4, 5] = [(1, 3), (2, 4)] := by decide
-}

{- @lean
theorem addWise_example : addWise [1, 2] [10, 20] = [11, 22] := by decide
-}

{- @lean
theorem split2_example : split2 [(1, 2), (3, 4)] = ([1, 3], [2, 4]) := by decide
-}
```

- [ ] **Step 4: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLibrary.hs
lake build GhcCoreToLean.Generated.ListLibrary
```

Expected: all properties so far `✅ Valid`. Observe names
(`grep -n "zip\|unzip" GhcCoreToLean/Generated/ListLibrary.lean`) and add any
differing qualified key to the same arm.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLibrary.hs
git commit -m "feat(lists): zip/zipWith/unzip"
```

---

### Task 7: Folds & predicates (`sum`, `product`, `all`, `any`, `and`, `or`)

**Files:**
- Modify: `GhcCoreToLean/Runtime.lean`, `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/ListLibrary.hs`

- [ ] **Step 1: Failing `#guard`s**

```lean
-- M1 Task 7: folds & predicates. Post-FTP these are Foldable methods, so the
-- desugarer resolves them through Data.Foldable.*; GHC.List.* hedged (as the
-- existing length/foldr mappings do). `sum` uses an explicit foldl, matching
-- GHC's `sum = foldl (+) 0` — not `List.sum`, whose instance surface we'd
-- rather not depend on. Haskell `all p xs` vs Lean `List.all xs p`: eta-wrap
-- swaps the order.
#guard Hs.and [true, true] == true
#guard Hs.and [true, false] == false
#guard Hs.and [] == true
#guard Hs.or [false, true] == true
#guard Hs.or [] == false
#guard valueMap "Data.Foldable.sum"     == some "(fun xs => List.foldl (· + ·) 0 xs)"
#guard valueMap "GHC.List.sum"          == some "(fun xs => List.foldl (· + ·) 0 xs)"
#guard valueMap "Data.Foldable.product" == some "(fun xs => List.foldl (· * ·) 1 xs)"
#guard valueMap "Data.Foldable.all"     == some "(fun p xs => List.all xs p)"
#guard valueMap "Data.Foldable.any"     == some "(fun p xs => List.any xs p)"
#guard valueMap "Data.Foldable.and"     == some "Hs.and"
#guard valueMap "Data.Foldable.or"      == some "Hs.or"
```

Run: `lake build GhcCoreToLean` — expected FAIL.

- [ ] **Step 2: Implement**

`Runtime.lean` (inside `namespace Hs`):

```lean
/-- Haskell `and :: [Bool] -> Bool`. `and [] = True`. -/
def and (xs : List Bool) : Bool := xs.all id

/-- Haskell `or :: [Bool] -> Bool`. `or [] = False`. -/
def or (xs : List Bool) : Bool := xs.any id
```

`Maps.lean` `valueMap`:

```lean
  -- Folds & predicates (Foldable methods post-FTP; GHC.List hedged).
  -- `sum`/`product` as explicit foldl matches GHC (`sum = foldl (+) 0`);
  -- `all`/`any` eta-wraps swap to Lean's (xs, p) order.
  | "Data.Foldable.sum"     | "GHC.List.sum"     => some "(fun xs => List.foldl (· + ·) 0 xs)"
  | "Data.Foldable.product" | "GHC.List.product" => some "(fun xs => List.foldl (· * ·) 1 xs)"
  | "Data.Foldable.all"     | "GHC.List.all"     => some "(fun p xs => List.all xs p)"
  | "Data.Foldable.any"     | "GHC.List.any"     => some "(fun p xs => List.any xs p)"
  | "Data.Foldable.and"     | "GHC.List.and"     => some "Hs.and"
  | "Data.Foldable.or"      | "GHC.List.or"      => some "Hs.or"
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 3: Extend the fixture**

Append to `examples/haskell/ListLibrary.hs`:

```haskell
sumList :: [Int] -> Int
sumList xs = sum xs

prodList :: [Int] -> Int
prodList xs = product xs

allPos :: [Int] -> Bool
allPos xs = all (> 0) xs

anyZero :: [Int] -> Bool
anyZero xs = any (== 0) xs

conj :: [Bool] -> Bool
conj bs = and bs

disj :: [Bool] -> Bool
disj bs = or bs

{- @lean
theorem sumList_example : sumList [1, 2, 3] = 6 := by decide
-}

{- @lean
theorem prodList_example : prodList [2, 3, 4] = 24 := by decide
-}

{- @lean
theorem allPos_example : allPos [1, 2] = true ∧ allPos [1, 0] = false := by decide
-}

{- @lean
theorem anyZero_example : anyZero [1, 0] = true ∧ anyZero [1, 2] = false := by decide
-}

{- @lean
theorem conj_disj_example : conj [] = true ∧ disj [] = false := by decide
-}
```

- [ ] **Step 4: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLibrary.hs
lake build GhcCoreToLean.Generated.ListLibrary
```

Expected: all properties `✅ Valid`. Observe names first
(`grep -n "sum\|product\|Foldable\|all\|any" GhcCoreToLean/Generated/ListLibrary.lean`);
sections `(> 0)`/`(== 0)` desugar to lambdas over already-mapped operators.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Runtime.lean GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLibrary.hs
git commit -m "feat(lists): sum/product/all/any/and/or (Foldable-qualified)"
```

---

### Task 8: Search & flatten (`elem`, `notElem`, `lookup`, `concat`, `concatMap`)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/ListLibrary.hs`

- [ ] **Step 1: Failing `#guard`s (mapping + semantic pins)**

```lean
-- M1 Task 8: search & flatten. Semantic pins for the Lean-side signatures we
-- rely on (contains/lookup use BEq — consistent with the project's Eq→BEq
-- convention; lookup's key-first order matches Haskell's).
-- Dot-notation pins: the receiver binds by TYPE, so these compile-and-hold
-- even if a future Lean flips explicit-argument order.
#guard ([1, 2, 3].contains 2) == true
#guard ([(1, 10), (2, 20)].lookup 2) == some 20
#guard ([[1], [2, 3]].flatten) == [1, 2, 3]
#guard ([1, 2].flatMap (fun x => [x, x])) == [1, 1, 2, 2]
#guard valueMap "Data.Foldable.elem"    == some "(fun x xs => xs.contains x)"
#guard valueMap "Data.Foldable.notElem" == some "(fun x xs => !(xs.contains x))"
#guard valueMap "GHC.List.lookup"       == some "(fun k ps => ps.lookup k)"
#guard valueMap "Data.Foldable.concat"  == some "List.flatten"
#guard valueMap "Data.Foldable.concatMap" == some "(fun f xs => xs.flatMap f)"
```

Run: `lake build GhcCoreToLean` — expected FAIL on the `valueMap` guards.
(If a *semantic pin* fails instead, the v4.24 signature differs from this
plan's assumption — fix the mapping string to match the real signature, keep
the pin asserting Haskell semantics, and update the `valueMap` guard to the
corrected string.)

- [ ] **Step 2: Implement in `Maps.lean` `valueMap`**

```lean
  -- Search & flatten. elem/notElem/lookup use BEq (the project's Eq image).
  -- Dot-notation binds the receiver by type, immune to arg-order drift.
  | "Data.Foldable.elem"    | "GHC.List.elem"    => some "(fun x xs => xs.contains x)"
  | "Data.Foldable.notElem" | "GHC.List.notElem" => some "(fun x xs => !(xs.contains x))"
  | "GHC.List.lookup"       | "Data.List.lookup" => some "(fun k ps => ps.lookup k)"
  | "Data.Foldable.concat"  | "GHC.List.concat"  => some "List.flatten"
  | "Data.Foldable.concatMap" | "GHC.List.concatMap" => some "(fun f xs => xs.flatMap f)"
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 3: Extend the fixture**

Append to `examples/haskell/ListLibrary.hs` (note `lookupOr` also exercises the
existing `fromMaybe` mapping):

```haskell
hasZero :: [Int] -> Bool
hasZero xs = elem 0 xs

misses :: Int -> [Int] -> Bool
misses x xs = notElem x xs

lookupOr :: Int -> [(Int, Int)] -> Int
lookupOr k ps = fromMaybe 0 (lookup k ps)

flattenAll :: [[Int]] -> [Int]
flattenAll xss = concat xss

dupEach :: [Int] -> [Int]
dupEach xs = concatMap (\x -> [x, x]) xs

{- @lean
theorem hasZero_example : hasZero [1, 0] = true ∧ hasZero [1, 2] = false := by decide
-}

{- @lean
theorem misses_example : misses 3 [1, 2] = true := by decide
-}

{- @lean
theorem lookupOr_example : lookupOr 2 [(1, 10), (2, 20)] = 20 ∧ lookupOr 9 [(1, 10)] = 0 := by decide
-}

{- @lean
theorem flattenAll_example : flattenAll [[1], [2, 3]] = [1, 2, 3] := by decide
-}

{- @lean
theorem dupEach_example : dupEach [1, 2] = [1, 1, 2, 2] := by decide
-}
```

`lookupOr` needs `import Data.Maybe (fromMaybe)` — add at the top of the
module, right after `module ListLibrary where`:

```haskell
import Data.Maybe (fromMaybe)
```

(`dupEach`'s lambda body `[x, x]` is a list literal — Task 3's `build` mapping
covers it.)

- [ ] **Step 4: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLibrary.hs
lake build GhcCoreToLean.Generated.ListLibrary
```

Expected: all properties `✅ Valid`. Observe names first
(`grep -n "elem\|lookup\|concat" GhcCoreToLean/Generated/ListLibrary.lean`).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLibrary.hs
git commit -m "feat(lists): elem/notElem/lookup/concat/concatMap"
```

---

### Task 9: Partial `maximum`/`minimum` (bottom path)

**Files:**
- Modify: `GhcCoreToLean/Maps.lean`, `GhcCoreToLean/Emit.lean` (~line 196), `GhcCoreToLean/Tests/Unit.lean`, `examples/haskell/ListLibrary.hs`

- [ ] **Step 1: Failing `#guard`s**

```lean
-- M1 Task 9: maximum/minimum are ⊥ ONLY on []. Like head/last they map to a
-- getD-default form: faithful on nonempty, `default` exactly where Haskell
-- is ⊥. List.max?/min? fold Max.max/Min.min — for user types the transpiler
-- already emits Min/Max consistent with derived Ord.
#guard ((List.max? [3, 1, 2]).getD 0) == 3
#guard ((List.min? ([] : List Int)).getD 7) == 7
#guard valueMap "Data.Foldable.maximum" == some "(fun xs => (List.max? xs).getD default)"
#guard valueMap "Data.Foldable.minimum" == some "(fun xs => (List.min? xs).getD default)"
```

Run: `lake build GhcCoreToLean` — expected FAIL on the `valueMap` guards.

- [ ] **Step 2: Implement**

`Maps.lean` `valueMap` (next to the other partials, `GHC.List.head` block):

```lean
  -- maximum/minimum: ⊥ only on []. Same getD-default partial-correctness
  -- route as head/last (registered in Emit.isPartialDefaultName so
  -- polymorphic defs get an [Inhabited t] binder).
  | "Data.Foldable.maximum" | "GHC.List.maximum" => some "(fun xs => (List.max? xs).getD default)"
  | "Data.Foldable.minimum" | "GHC.List.minimum" => some "(fun xs => (List.min? xs).getD default)"
```

`Emit.lean` `isPartialDefaultName` (~line 196) becomes:

```lean
private def isPartialDefaultName : Name → Bool
  | "GHC.List.head" | "GHC.List.last" | "GHC.List.!!"
  | "Data.Maybe.fromJust"
  | "Data.Foldable.maximum" | "GHC.List.maximum"
  | "Data.Foldable.minimum" | "GHC.List.minimum" => true
  | _ => false
```

Run: `lake build GhcCoreToLean` — expected PASS.

- [ ] **Step 3: Extend the fixture**

Append to `examples/haskell/ListLibrary.hs`:

```haskell
maxOf :: [Int] -> Int
maxOf xs = maximum xs

minOf :: [Int] -> Int
minOf xs = minimum xs

{- @lean
theorem maxOf_example : maxOf [3, 1, 2] = 3 := by decide
-}

{- @lean
theorem minOf_example : minOf [3, 1, 2] = 1 := by decide
-}
```

- [ ] **Step 4: End-to-end**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/ListLibrary.hs
lake build GhcCoreToLean.Generated.ListLibrary
```

Expected: all ListLibrary properties `✅ Valid`. Observe names
(`grep -n "maximum\|minimum" GhcCoreToLean/Generated/ListLibrary.lean`).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Maps.lean GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/ListLibrary.hs
git commit -m "feat(lists): partial maximum/minimum via getD-default bottom path"
```

---

### Task 10: README update + full regression

**Files:**
- Modify: `README.md` (Limitations section)

- [ ] **Step 1: Update the Limitations section**

In the bullet listing the mapped `base` surface, replace:

```markdown
  (`&& || not otherwise`), combinators (`id . const flip $`), the total list
  library (`++ map filter foldr foldl length reverse null`), 2-tuples
  (`fst snd`, construction, patterns), and `Maybe`/`Either` eliminators
```

with:

```markdown
  (`&& || not otherwise`), combinators (`id . const flip $`), the total list
  library (`++ map filter foldr foldl length reverse null take drop splitAt
  replicate zip zipWith unzip sum product all any and or elem notElem lookup
  concat concatMap`), list literals (`[a, b, c]`) and `Int` ranges
  (`[a..b]`, `[a,b..c]` — the zero-stride `[a,a..c]` with `c ≥ a` is infinite
  in Haskell and lowers to `default`), 2-/3-/4-tuples (`fst snd`, construction,
  patterns), and `Maybe`/`Either` eliminators
```

In the partial-functions bullet, change:

```markdown
  (`head`, `tail`, `init`, `last`, `!!`, `fromJust`) are ⊥ *only* on the
```

to:

```markdown
  (`head`, `tail`, `init`, `last`, `!!`, `fromJust`, `maximum`, `minimum`)
  are ⊥ *only* on the
```

Replace the final bullet:

```markdown
- Not yet supported: 3-tuple *construction* (type and pattern work; a
  constructed 3-tuple is a loud compile error), and Haskell list-literal syntax
  (`[a, b, c]` desugars to `GHC.Base.build`).
  Theorems over lists/recursion need a user-written `induction` proof — bare
  `by blaster` (SMT) discharges only quantifier-free arithmetic goals.
```

with:

```markdown
- Not yet supported: 5+-tuple construction, and the infinite list producers
  (`iterate`, `repeat`, `cycle`, `enumFrom`, `enumFromThen`) — all loud
  compile errors by design.
  Theorems over lists/recursion need a user-written `induction` proof — bare
  `by blaster` (SMT) discharges only quantifier-free arithmetic goals;
  concrete-value list properties close with `by decide`.
```

- [ ] **Step 2: Full regression — every fixture this milestone touched plus the pre-existing examples**

```bash
lake build   # library (#guards) + Spike examples + binary
for f in TupleTriple ListLiterals ListLibrary Ratio ListBasics TupleBasics PartialHead NumOrd OperatorCommons Arithmetic UserClass; do
  ./transpile.sh examples/haskell/$f.hs && lake build GhcCoreToLean.Generated.$f || { echo "FAIL: $f"; break; }
done
```

Expected: every module transpiles, builds, and its properties report
`✅ Valid` (PartialHead/ListBasics include user-written induction proofs —
they must still verify).

- [ ] **Step 3: Commit**

```bash
git add README.md
git commit -m "docs: M1 lists & tuples — README coverage/limitations update"
```

---

## Milestone gate (after Task 10)

- Invoke `superpowers:requesting-code-review` on the branch diff.
- Open a PR (`gh pr create`) titled "M1: lists & tuples completion" referencing
  the spec, per the finishing-a-development-branch flow.
- User checkpoint: review + merge decision before starting the M2 plan.
