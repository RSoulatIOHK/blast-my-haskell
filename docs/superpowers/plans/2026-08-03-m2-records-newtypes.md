# M2 — Records & Newtypes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make record construction/update/selectors and (fully-erased) newtypes transpile and verify end-to-end, per the approved spec [2026-07-24-coverage-roadmap-design.md](../specs/2026-07-24-coverage-roadmap-design.md) §M2 — with three spec corrections discovered by pre-planning exploration (below).

**Architecture:** Records are already mostly supported (decls emit as Lean `inductive`; GHC-generated selectors arrive as ordinary Core defs and emit as `def`s — proven by `Generated/Arithmetic.lean`); the record half is a fixture-driven audit. Newtypes need four coordinated changes: a shim `ECoercion` fix (currently an unparseable JSON stub), value-level coercion-argument erasure in `Lower`, type-level erasure as a **string-resolution pass** in `Emit` (not `typeConMap` — emitted type strings double as instance-matching keys), and manifest suppression in `transpile_graph.py`. A loud-fail guard rejects *any* instance on a newtype.

**Tech Stack:** Lean 4 (`v4.24.0`), `lake`; GHC 9.2.7 + cabal (`shim/` — this milestone touches Haskell shim code, rebuild with `cd shim && cabal build`); Python (`scripts/transpile_graph.py`); Blaster.

**Branch:** `feature/m2-records-newtypes`, stacked on `feature/m1-lists-tuples` (PR #3). The M2 PR targets `main` after #3 merges.

---

## Spec corrections (validated by exploration; override §M2 where they conflict)

1. **"Value-level coercions are already erased" is only half-true.** `Lower.lean:58` strips `.cast` in *head* position, but (a) the shim's `ECoercion` arm ([shim/Main.hs:200](../../../shim/Main.hs)) emits `{"tag":"Cast","expr":{}}` which `Parse.lean:142-144` CANNOT parse (hard abort — the path has never been exercised: 0 `"Cast"` tags across all 24 existing dumps), and (b) `Lower.isTypeOrDictArg` does not erase a coercion in *argument* position.
2. **Type-level erasure belongs in the string-resolution passes** (`resolveUserTypes` layer — see the "Name-resolution post-passes" header in `Emit.lean`), not `typeConMap`: `derivedEqTypes`/`ordTypes`/`findClassMethod` all use emitted type strings as identity keys, so erasing `Age`→`Int` early would cross-match instances on `Age` with instances on `Int`. Keep `(GHCCore.tyConOpaque "Age")` distinct through matching; rewrite at the end.
3. **The "hand-written instance on a newtype errors; `deriving` is fine" rule is not implementable** from current data: `tcg_insts` carries no derived-vs-hand-written marker, and GND instances have no `$c` method bindings to sniff. Sound M2 rule: **ANY instance whose head type is a newtype → transpiler error** (loud), with a message telling the user to write the property against the underlying type. Relaxable later by extending the decl-plugin to dump instance origin.

**Also documented (not fixed here):** parameterized data types (`data Box a = …`) emit broken-but-loud output (the decl-plugin dumps no type parameters) — M2 fixtures stay monomorphic; this is a recorded limitation, not an M2 deliverable.

## Soundness discipline (unchanged)

Loud-fail is safe; silent-wrong is never acceptable. Newtype erasure is sound *because* Core semantics already identify the newtype with its underlying type; the instance guard exists precisely because a hand-written instance is the one place erasure could silently change meaning.

## Name/shape-observation rule

Same as M1: fixtures transpile FIRST; read `/tmp/transpile-<Mod>.json` (and `.transpile-sandbox/<Mod>.decls.json`) before writing mappings; record observations (including negatives) in `Tests/Unit.lean` comments; hedge keys are never removed. **New for M2:** the load-bearing unknown is the *Core shape of newtype wrap/unwrap at pass-0000 through ghc-dump* — Task 3 exists to observe it before Tasks 4-5 commit to a mechanism.

## Per-task dev loop

Edit → `lake build GhcCoreToLean` (#guards) → `lake build ghccoretolean` → (if shim changed: `cd shim && cabal build`) → `./transpile.sh examples/haskell/<Mod>.hs` → `lake build GhcCoreToLean.Generated.<Mod>`. Re-transpile before trusting any build. `decide` for ground goals, `blaster` for quantified; `✅ Valid` prints only for blaster.

---

## File Structure

- **Modify** [shim/Main.hs](../../../shim/Main.hs) — `ECoercion` emits a parseable token.
- **Modify** [GhcCoreToLean/AST.lean](../../../GhcCoreToLean/AST.lean) — `Expr.coercion` atom.
- **Modify** [GhcCoreToLean/Parse.lean](../../../GhcCoreToLean/Parse.lean) — parse the token.
- **Modify** [GhcCoreToLean/Lower.lean](../../../GhcCoreToLean/Lower.lean) — erase coercion arguments.
- **Modify** [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — newtype suppression (decl emission, `ctorNames`, `resolveUserCtors`), `resolveNewtypes` pass, newtype-instance guard, crib fix.
- **Modify** [scripts/transpile_graph.py](../../../scripts/transpile_graph.py) — manifest suppression for newtypes.
- **Modify** [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean) — per-task `/-! ## M2 Task N -/` sections.
- **Create** `examples/haskell/RecordOps.hs`, `examples/haskell/NewtypeBasic.hs`, `examples/haskell/NewtypeInstances.hs` (negative), `examples/haskell/RecordClient.hs` (cross-module).
- **Modify** [README.md](../../../README.md) — Limitations (final task).

---

### Task 1: Records audit — `RecordOps.hs` (fixture-driven; expected mostly green)

**Files:** Create `examples/haskell/RecordOps.hs`; modify `GhcCoreToLean/Tests/Unit.lean` (+ whatever the fixture surfaces).

- [ ] **Step 1: Create the fixture** — labeled construction, multi-field update, selector used first-class, nested record type:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module RecordOps where

data Point = Point { px :: Int, py :: Int }

data Rect = Rect { topLeft :: Point, width :: Int, height :: Int }

mkPoint :: Int -> Int -> Point
mkPoint x y = Point { px = x, py = y }

shiftX :: Int -> Point -> Point
shiftX d p = p { px = px p + d }

resize :: Int -> Int -> Rect -> Rect
resize w h r = r { width = w, height = h }

xs :: [Point] -> [Int]
xs ps = map px ps

area :: Rect -> Int
area r = width r * height r

{- @lean
theorem mkPoint_px : ∀ (x y : Int), px (mkPoint x y) = x := by blaster
-}

{- @lean
theorem shiftX_moves : ∀ (d x y : Int), px (shiftX d (mkPoint x y)) = x + d := by blaster
-}

{- @lean
theorem shiftX_keeps_py : ∀ (d x y : Int), py (shiftX d (mkPoint x y)) = y := by blaster
-}

{- @lean
theorem resize_area : ∀ (w h : Int), area (resize w h (Rect (Point 0 0) 1 1)) = w * h := by blaster
-}

{- @lean
theorem xs_example : xs [mkPoint 1 2, mkPoint 3 4] = [1, 3] := by decide
-}
```

- [ ] **Step 2: Transpile and audit**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/RecordOps.hs
lake build GhcCoreToLean.Generated.RecordOps
```

Expected (hypothesis): labeled construction desugars to positional ctor application; update desugars to case-and-rebuild; selectors arrive as Core defs — all already-supported shapes. Read the generated file: `Point`/`Rect` as `inductive`, `def px`/`py`/`topLeft`/`width`/`height`, no residue.

- [ ] **Step 3: Fix what breaks (if anything).** Scope rule from the spec: only what the fixture surfaces. Diagnose via the shim JSON; apply the M1 observed-names discipline for any unmapped name; anything structural (beyond a mapping) gets its own `#guard`s. If NOTHING breaks, record that result in a `/-! ## M2 Task 1 -/` Unit.lean comment (the audit outcome is the deliverable): which record features were exercised and that they desugar to already-supported Core.

- [ ] **Step 4: Verify all 5 properties** (4 × `✅ Valid` + 1 decide compiles). If blaster stalls on the record goals, fall back per-goal to `by intro ...; rfl` and report.

- [ ] **Step 5: Commit**

```bash
git add examples/haskell/RecordOps.hs GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(records): record construction/update/selector audit fixture (RecordOps)"
```

(Include any surfaced-fix files in the same commit, described in the message body.)

---

### Task 2: Shim `ECoercion` fix + coercion-argument erasure

**Files:** Modify `shim/Main.hs`, `GhcCoreToLean/AST.lean`, `GhcCoreToLean/Parse.lean`, `GhcCoreToLean/Lower.lean`, `GhcCoreToLean/Tests/Unit.lean`.

- [ ] **Step 1: Failing parse/lower `#guard`s** (`/-! ## M2 Task 2 — coercion token -/`):

```lean
-- A Coercion in ARGUMENT position must be erased like a type/dict arg:
-- `f (co :: Coercion)` → `f`. In head position it cannot occur (a coercion
-- is not a function); Emit loud-fails if one survives.
#guard (Lower.lowerExpr (.app
          (.var {name := "f", unique := 1, ty := .tyVar "a", role := .id})
          .coercion))
       == (.var {name := "f", unique := 1, ty := .tyVar "a", role := .id})
```

(Adapt the equality to the AST's BEq derivation — check whether `Expr` derives `BEq`; if not, compare via `emitExpr` strings like the existing Lower-adjacent guards do.)

Run: `lake build GhcCoreToLean` — FAIL (no `Expr.coercion`).

- [ ] **Step 2: Implement**

`AST.lean`: add `| coercion : Expr` to the `Expr` inductive (next to `.type_`).
`Parse.lean` (~142): replace the `"Cast"` arm's body-parse with a `"Coercion"` arm producing `.coercion` (keep a `"Cast"` arm parsing `expr` for compatibility IF the old shape could still appear — it cannot per exploration, but parsing `{"tag":"Cast"}` with a *present* well-formed `expr` is harmless; make the `{}` case produce `.coercion` instead of aborting).
`Lower.lean`: extend `isTypeOrDictArg` with `| .coercion => true`.
`shim/Main.hs:200`: `ECoercion -> object [ "tag" .= ("Coercion" :: T.Text) ]`.

- [ ] **Step 3: Rebuild everything, regression**

```bash
lake build GhcCoreToLean            # guards pass
( cd shim && cabal build )          # shim rebuild — REQUIRED, Task 3 depends on it
lake build ghccoretolean
./transpile.sh examples/haskell/Ratio.hs && lake build GhcCoreToLean.Generated.Ratio
```

Expected: everything green (the token is not yet produced by any fixture — this is pure plumbing; the regression proves nothing broke).

- [ ] **Step 4: Commit**

```bash
git add shim/Main.hs GhcCoreToLean/AST.lean GhcCoreToLean/Parse.lean GhcCoreToLean/Lower.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "fix(shim): parseable Coercion token; Lower erases coercion arguments"
```

---

### Task 3: Newtype observation — `NewtypeBasic.hs` (observe FIRST, then implement value level)

**Files:** Create `examples/haskell/NewtypeBasic.hs`; modify per observation.

- [ ] **Step 1: Create the fixture**

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module NewtypeBasic where

newtype Age = Age Int

mkAge :: Int -> Age
mkAge n = Age n

getAge :: Age -> Int
getAge (Age n) = n

addAges :: Age -> Age -> Age
addAges a b = Age (getAge a + getAge b)

{- @lean
theorem addAges_sum : ∀ (a b : Int), getAge (addAges (mkAge a) (mkAge b)) = a + b := by blaster
-}
```

- [ ] **Step 2: Transpile and OBSERVE (do not fix yet)**

```bash
lake build ghccoretolean
./transpile.sh examples/haskell/NewtypeBasic.hs   # may fail — that's data
python3 -m json.tool /tmp/transpile-NewtypeBasic.json | grep -n -A3 -B3 "Age\|Coercion\|Cast" | head -80
cat .transpile-sandbox/NewtypeBasic.decls.json
```

Record in the eventual Unit.lean comment: (a) how newtype construction appears in Core post-ghc-dump (bare value? cast-wrapped? `Age` ctor application?); (b) how the pattern-match in `getAge` appears (case on `Age` ctor? direct binding?); (c) whether `Coercion` tokens appear; (d) the decls.json entry (`kind:"newtype"`, field shape).

- [ ] **Step 3: Implement the VALUE level per observation.** Decision rules:
  - If ghc-dump already erased wrap/unwrap (construction = bare value, match = direct): nothing to do at value level — record the negative result.
  - If the `Age` ctor appears in value position: it must map to identity — but do NOT add a global `dataConMap` arm (name collision risk with user data ctors); handle via the newtype-aware `ctorNames`/emission path in Task 4 (the ctor set comes from `typeDecls` where `kind == "newtype"`).
  - If `Age` appears as a case alt pattern: single-ctor single-field case → the same shape as the existing unwrapping-ctor erasure (`Lower.lean:44-53`, `I#` handling) — extend `isUnwrappingDataCon`-style logic with a *program-derived* newtype-ctor set rather than the static list (this changes `lowerProgram`'s signature to take the newtype ctor set; thread it from `Main.lean`).
  - Anything else: report the shape verbatim and stop for controller review (status DONE_WITH_CONCERNS on the observation, no invented mechanism).

- [ ] **Step 4: e2e will still loud-fail on the TYPE level** (`(GHCCore.tyConOpaque "Age")` or bare `Age` refs) — that is Task 4's job. This task's exit criterion: the JSON parses (Task 2), the value-level story is implemented + `#guard`-pinned (or recorded as nothing-to-do), and the remaining failure is exactly the type-level reference.

- [ ] **Step 5: Commit** (`feat(newtypes): value-level handling per pass-0000 observation` — adjust to what was done).

---

### Task 4: Newtype type-level erasure (resolution pass) + decl/manifest suppression

**Files:** Modify `GhcCoreToLean/Emit.lean`, `scripts/transpile_graph.py`, `GhcCoreToLean/Tests/Unit.lean`.

- [ ] **Step 1: Failing `#guard`s** (`/-! ## M2 Task 4 — newtype erasure -/`). Pin the new pass at the string level (exact helper signature to be matched to Emit's existing pass style):

```lean
-- resolveNewtypes rewrites an opaque newtype tycon to its UNDERLYING type
-- string, AFTER instance matching (which uses opaque strings as keys) and
-- alongside resolveUserTypes. Underlying type comes from the decl's single
-- ctor's single field.
#guard resolveNewtypes [("Age", "Int")] "(x : (GHCCore.tyConOpaque \"Age\"))" == "(x : Int)"
#guard resolveNewtypes [("Age", "Int")] "(GHCCore.tyConOpaque \"Wage\")" == "(GHCCore.tyConOpaque \"Wage\")"  -- no substring bleed
```

- [ ] **Step 2: Implement in Emit.lean:**
  1. `newtypeDecls (p : Program) : List (Name × String)` — decls with `kind == "newtype"`, paired with `emitType` of their single ctor's single field (loud `panic!`-free error path if a "newtype" has ≠1 ctor or ≠1 field — malformed dump).
  2. `resolveNewtypes` — same string-replacement idiom as `resolveUserTypes` (`Emit.lean`, `def resolveUserTypes`), applied at every site `resolveUserTypes` is applied (bodies, instance block, spec text via `resolveSpecText`), immediately after it.
  3. Suppress newtypes from: the `datas` emission map (`Emit.lean`, search `let datas :=` inside `emitFullProgram`), `ctorNames` (same function, its first `let`), and `resolveUserCtors`'s decl set. The newtype CTOR in value position (if Task 3 found it appears) resolves to identity here: emit `(fun x => x)`/`id` for ctor refs whose ctor belongs to a newtype. NOTE: keep newtypes in `sortDataDecls`' input; filter at the emission map only (see the Name-resolution post-passes header in Emit.lean) — dependency chains thread through newtypes transitively (`Point` → `Wrapper`(newtype) → `Q`), so filtering before the sort loses the chain and reintroduces the forward-reference bug.
  4. Crib fix (`Main.lean:60-66`): print `newtype {name} (erased → {underlying})` instead of `data {name}`.
- [ ] **Step 3: Manifest suppression** — `scripts/transpile_graph.py:106-109`: skip `typeDecls` entries with `kind == "newtype"` when writing `EXT_TYPES_MANIFEST` (else `resolveExternalTypes` rewrites `Age` → `NewtypeBasic.Age`, which no longer exists). Note the decls.json must carry `kind` through the graph script — check what it reads and extend if it consumes a reduced form.
- [ ] **Step 4: e2e**

```bash
lake build GhcCoreToLean && lake build ghccoretolean
./transpile.sh examples/haskell/NewtypeBasic.hs
lake build GhcCoreToLean.Generated.NewtypeBasic
```

Expected: `mkAge : Int → Int`, `getAge : Int → Int` (identity-ish bodies), `addAges : Int → Int → Int`; theorem `✅ Valid`. No `Age` anywhere in the generated file. Then full-fixture regression sweep (M1's collect-don't-break loop) to prove zero churn on non-newtype modules.

- [ ] **Step 5: Commit** (`feat(newtypes): full type-level erasure via resolveNewtypes pass`).

---

### Task 5: Newtype-instance loud-fail guard — `NewtypeInstances.hs` (negative fixture)

**Files:** Modify `GhcCoreToLean/Emit.lean` (or `Main.lean` — wherever `Program`-level validation best fits), `GhcCoreToLean/Tests/Unit.lean`; create `examples/haskell/NewtypeInstances.hs`.

- [ ] **Step 1: Failing `#guard`** on the detection function:

```lean
-- ANY instance whose head tycon is a newtype is rejected (loud): erasure
-- cannot represent it, and derived-vs-hand-written is indistinguishable in
-- tcg_insts (GND instances carry no $c methods to sniff). Relaxable later
-- via a decl-plugin origin dump.
#guard (newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "Age" []], dfunName := "$fEqAge", dfunUnique := 0}]
         [("Age", "Int")]).length == 1
#guard (newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "Point" []], dfunName := "$fEqPoint", dfunUnique := 0}]
         [("Age", "Int")]) == []
```

(Match the actual `Instance` structure fields from `AST.lean` — adjust literal syntax accordingly.)

- [ ] **Step 2: Implement** `newtypeInstanceViolations` + wire into `emitFullProgram` (or `Main.lean` before emission): on violation, the transpiler exits with a clear error naming the instance, the newtype, and the remedy ("newtypes are erased to their underlying type; write the instance/property against `Int`, or drop the instance").
- [ ] **Step 3: Negative fixture**

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module NewtypeInstances where

newtype Celsius = Celsius Int

instance Eq Celsius where
  (Celsius a) == (Celsius b) = a == b

sameTemp :: Celsius -> Celsius -> Bool
sameTemp a b = a == b
```

```bash
./transpile.sh examples/haskell/NewtypeInstances.hs; echo "exit: $?"
```

Expected: NON-zero exit, error message names `Eq`/`Celsius`. This fixture is deliberately excluded from the green-regression list — add a header comment saying so (`-- NEGATIVE fixture: transpilation MUST fail; exercised manually / by the M2 regression script's expected-fail list`).

- [ ] **Step 4: Commit** (`feat(newtypes): loud-fail guard for instances on newtypes + negative fixture`).

---

### Task 6: Cross-module records & newtypes — `RecordClient.hs`

**Files:** Create `examples/haskell/RecordClient.hs`; modify per what breaks (expected: nothing or manifest-level only).

- [ ] **Step 1: Fixture importing Task 1's and Task 3's modules:**

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module RecordClient where

import RecordOps (Point, mkPoint, px)
import NewtypeBasic (Age, mkAge, getAge)

originDist :: Point -> Int
originDist p = px p

clientAge :: Int -> Int
clientAge n = getAge (mkAge n)

{- @lean
theorem clientAge_id : ∀ (n : Int), clientAge n = n := by blaster
-}

{- @lean
theorem originDist_mk : ∀ (x y : Int), originDist (mkPoint x y) = x := by blaster
-}
```

- [ ] **Step 2: e2e** — `./transpile.sh examples/haskell/RecordClient.hs` (transitively transpiles deps), build. This is the proof that: imported record selectors qualify correctly (`RecordOps.px`), the manifest carries `Point` but NOT `Age` (Task 4 suppression), and an imported newtype-typed signature (`Age` in `clientAge`'s Core type) erases to `Int` across module boundaries. Check the generated import lines and the absence of `Age` anywhere.
- [ ] **Step 3: Commit** (`test(m2): cross-module record selectors + imported-newtype erasure`).

---

### Task 7: README + full regression + milestone gate

**Files:** Modify `README.md`.

- [ ] **Step 1: README Limitations update:**
  - Mapped-surface/features: add "records (labeled construction, record-update syntax, selectors as first-class functions — decls emit as Lean `inductive` with selector `def`s)" and "newtypes (fully erased to the underlying type; theorems quantify over the underlying type)".
  - New limitation bullets: "Any type-class instance on a newtype is a loud transpiler error (erasure cannot represent it; write properties against the underlying type)." and "Parameterized data types (`data Box a = …`) are not yet dumped with their type parameters — loud compile error." and: "In `@lean` spec text, a data constructor applied to a **bare variable** (`Point x y`) is not qualified and fails loud (`function expected at Point`) — parenthesise or use literal arguments (`Point (f x) y`, `Point 1 2`). `isArgStart` deliberately excludes lowercase letters so that `instance : BEq Point where` is never mis-read as a constructor application; see the `replaceCtorApps` docstring and the M2 Task 1 guards in `Tests/Unit.lean`."
- [ ] **Step 2: Full regression** — M1's collect-don't-break loop over all committed fixtures PLUS the new ones, with `NewtypeInstances` on an expected-fail list:

```bash
lake build GhcCoreToLean && lake build ghccoretolean
fails=""
for f in $(git ls-files 'examples/haskell/*.hs' 'examples/haskell/**/*.hs'); do
  m=$(basename $f .hs)
  case $m in NewtypeInstances) continue;; esac
  ./transpile.sh "$f" && lake build GhcCoreToLean.Generated.$m || fails="$fails $m"
done
./transpile.sh examples/haskell/NewtypeInstances.hs && fails="$fails NewtypeInstances(SHOULD-HAVE-FAILED)"
echo "FAILURES:$fails"
```

Known-red at HEAD: `UserClass` (pre-existing false theorem — report, don't fix, unless the user has resolved it by then; check first). Working-tree user edits: test on-disk state, commit nothing foreign.

- [ ] **Step 3: Commit** (`docs: M2 records & newtypes — README coverage/limitations update`), then milestone gate: final whole-branch review subagent → `gh pr create` (base: `feature/m1-lists-tuples` if #3 unmerged, else `main`) titled "M2: records & newtypes" → user checkpoint.

---

## Self-review notes (writing-plans checklist)

- **Spec coverage:** records audit (T1, T6) ✓; newtype erasure (T2-T4, T6) ✓; loud-fail instance guard (T5) ✓; fixtures RecordOps/NewtypeBasic/NewtypeInstances per spec ✓ + RecordClient (cross-module, spec's "cross-module selector use") ✓; README (T7) ✓.
- **Observation-driven steps** (T1 S3, T3 S3) carry explicit decision rules and stop conditions instead of invented mechanisms — this is deliberate, mirroring the spec's "scope is what the fixture surfaces".
- **Guard code blocks** reference helper names (`resolveNewtypes`, `newtypeInstanceViolations`) that Tasks define; exact literal syntax must be adapted to `AST.lean`'s actual structures at implementation time (flagged inline where so).
