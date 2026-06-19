# Type Classes & Instances (Tier 3) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Grow instance/typeclass support beyond the single `Eq`→`BEq` wiring — adding `Ord` and `Show` instance emission now, and scoping (via a design spike) the larger effort of **user-defined classes + dictionary passing**.

**Architecture:** Tasks 1–3 extend the existing pattern in [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) `emitInstance`, which already finds a class method's `$c…` binding by matching the instance head type ([`findEqMethod`](../../../GhcCoreToLean/Emit.lean)). They are concrete, low-risk, and mirror existing code. Task 4 is a **design spike**: today dictionaries are *erased* in [Lower.lean](../../../GhcCoreToLean/Lower.lean) and there is no `class` declaration in the AST, so supporting user-defined classes is a new subsystem that needs its own brainstorming pass before it can be planned at step granularity. Task 4's deliverable is that sub-spec, not code.

**Tech Stack:** Lean 4 `v4.24.0`, `lake`; GHC 9.2.7 for end-to-end transpiles; the `decl-plugin` JSON sidecar that already supplies `Instance` records ([AST.lean](../../../GhcCoreToLean/AST.lean) `Instance`).

**Dependency:** Do Tier 1–2 first (the [base-coverage plan](2026-06-18-base-coverage-tiers-1-2.md)) — `Ordering` (Task 3 there) and the `#guard` harness (Task 0 there) are prerequisites for the guards below.

---

## File Structure

- **Modify** [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — generalize the method finder; add `Ord` and `Show` arms to `emitInstance`.
- **Modify** [GhcCoreToLean/Tests/Unit.lean](../../../GhcCoreToLean/Tests/Unit.lean) — guards for the new instance emitters.
- **Create** `examples/haskell/OrdInstance.hs` — end-to-end fixture.
- **Create** `docs/superpowers/plans/<date>-userclasses-dictionaries.md` — produced by Task 4 (the spike), not pre-written here.

---

## Task 1: Generalize the instance-method finder

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (`findEqMethod` → `findClassMethod`)
- Test: `GhcCoreToLean/Tests/Unit.lean`

`findEqMethod` is hard-coded to `$c==`. Generalize it to take the method name so `Ord`/`Show` can reuse the head-type disambiguation. Keep behavior identical for `Eq`.

- [ ] **Step 1: Write the failing guard** (drive it through `emitInstance` `Eq`, which must still work after the refactor)

```lean
-- Task 1: Eq instance emission is unchanged by the finder refactor.
def eqInstProgram : CoreProgram :=
  [ .nonRec {name := "$c==", unique := 50,
             ty := .tyFun (.tyCon "Foo" []) (.tyFun (.tyCon "Foo" []) (.tyCon "Bool" [])),
             role := .id}
            (.lam {name := "a", unique := 1, ty := .tyCon "Foo" [], role := .id}
                  (.lit (.litInt 0))) ]
def eqInst : Instance :=
  {className := "Eq", headTypes := [.tyCon "Foo" []], dfunName := "$fEqFoo", dfunUnique := 99}
#guard (emitInstance eqInstProgram eqInst).isSome
#guard ((emitInstance eqInstProgram eqInst).getD "").splitOn "instance : BEq Foo" |>.length == 2
```

- [ ] **Step 2: Run to verify it passes today** (this guards against regression — it should already pass)

Run: `lake build GhcCoreToLean`
Expected: PASS now. (We write the regression guard first, then refactor under it.)

- [ ] **Step 3: Refactor — rename and parameterize**

In [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean), replace `findEqMethod` with a method-name-parameterized version:

```lean
/-- Find the `$c<method>` binding belonging to the instance whose head type
    matches `headTyStr`, returning its emitted (unique-suffixed) def name.
    Generalizes the former `findEqMethod`: multiple instances of a class each
    produce a `$c<method>` binding that collides after sanitization, so we
    disambiguate by matching the method's first value-argument type against the
    instance head. -/
private def findClassMethod (binds : CoreProgram) (method : Name) (headTyStr : String) : Option String :=
  let matchesHead (v : Var) : Bool :=
    v.name == method &&
      (match firstValArgTy v.ty with
       | some t => emitType t == headTyStr
       | none   => false)
  binds.findSome? fun b => match b with
    | .nonRec v _ => if matchesHead v then some (localId v) else none
    | .rec_ pairs => (pairs.find? (fun (v, _) => matchesHead v)).map (fun (v, _) => localId v)
```

Update the `Eq` arm of `emitInstance` to call it:

```lean
  | "Eq" =>
    match findClassMethod binds "$c==" tyStr with
    | some methodRef => some s!"instance : BEq {tyStr} where\n  beq := {methodRef}"
    | none           => none
```

- [ ] **Step 4: Run to verify still passing**

Run: `lake build GhcCoreToLean`
Expected: PASS (the regression guard from Step 1 still holds).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "refactor: generalize findEqMethod to findClassMethod(method, head)"
```

---

## Task 2: `Ord` → Lean `Ord` instance

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (`emitInstance`)
- Test: `GhcCoreToLean/Tests/Unit.lean`, end-to-end

GHC's `Ord` instance provides `$ccompare : T → T → Ordering`. Lean's `Ord` class needs `compare : T → T → Ordering`. With `Ordering` already mapped (Tier-2 Task 3) this is a direct wiring, mirroring `Eq`→`BEq`.

- [ ] **Step 1: Write the failing guard**

```lean
-- Task 2: Ord instance emits a Lean `Ord` instance from `$ccompare`.
def ordInstProgram : CoreProgram :=
  [ .nonRec {name := "$ccompare", unique := 60,
             ty := .tyFun (.tyCon "Foo" []) (.tyFun (.tyCon "Foo" []) (.tyCon "Ordering" [])),
             role := .id}
            (.lam {name := "a", unique := 1, ty := .tyCon "Foo" [], role := .id}
                  (.var {name := "GHC.Types.EQ", unique := 2, ty := .tyCon "Ordering" [], role := .id})) ]
def ordInst : Instance :=
  {className := "Ord", headTypes := [.tyCon "Foo" []], dfunName := "$fOrdFoo", dfunUnique := 98}
#guard ((emitInstance ordInstProgram ordInst).getD "").splitOn "instance : Ord Foo" |>.length == 2
#guard ((emitInstance ordInstProgram ordInst).getD "").splitOn "compare :=" |>.length == 2
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build GhcCoreToLean`
Expected: FAIL — `Ord` currently falls through to `| _ => none`, so `emitInstance` returns `none` and `.getD ""` is empty.

- [ ] **Step 3: Implement — add the `Ord` arm**

In `emitInstance`, add before `| _ => none`:

```lean
  | "Ord" =>
    match findClassMethod binds "$ccompare" tyStr with
    | some methodRef => some s!"instance : Ord {tyStr} where\n  compare := {methodRef}"
    | none           => none
```

- [ ] **Step 4: Run unit guards**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: End-to-end fixture**

Add `examples/haskell/OrdInstance.hs`:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module OrdInstance where
    import Prelude

    data Coin = Heads | Tails deriving (Eq, Ord)

    pick :: Coin -> Coin -> Coin
    pick a b = if a <= b then a else b
```

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/OrdInstance.hs && lake build GhcCoreToLean.Generated.OrdInstance`
Expected: PASS — an `instance : Ord Coin` is emitted and `pick`'s `<=` resolves through it. (If GHC's derived `Ord` desugars `$ccompare` via the `Enum` tag rather than a self-contained body, record the emitted form; the head-type match may need the `$ccompare`'s first *value* arg, which `firstValArgTy` already skips foralls/dicts to find.)

- [ ] **Step 6: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean examples/haskell/OrdInstance.hs
git commit -m "feat: emit Lean Ord instance from GHC Ord ($ccompare)"
```

---

## Task 3: `Show` → Lean `ToString`/`Repr` instance (counterexample readability)

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (`emitInstance`)
- Test: `GhcCoreToLean/Tests/Unit.lean`

Blaster counterexamples print emitted values; user types already `derive Repr` ([Emit.lean](../../../GhcCoreToLean/Emit.lean) `emitDataDecl`), so this is mostly about not *dropping* a user `Show` instance silently. GHC's `$cshowsPrec`/`$cshow` bodies are stringly and rarely match Lean's `ToString`; the safe, sound choice is to **ignore the GHC body and rely on the derived `Repr`** rather than mis-emit a `Show`. This task makes that decision explicit and documented rather than an accidental `none`.

- [ ] **Step 1: Write the guard — `Show` is intentionally skipped (returns `none`)**

```lean
-- Task 3: Show instances are intentionally not wired (derived Repr covers printing).
def showInst : Instance :=
  {className := "Show", headTypes := [.tyCon "Foo" []], dfunName := "$fShowFoo", dfunUnique := 97}
#guard emitInstance [] showInst == none
```

- [ ] **Step 2: Run to verify it passes today** (it already returns `none` via the catch-all)

Run: `lake build GhcCoreToLean`
Expected: PASS now.

- [ ] **Step 3: Make the skip explicit and documented**

In `emitInstance`, add an explicit arm before `| _ => none` so the intent is recorded (behavior identical, but no longer an accident):

```lean
  -- Show is deliberately not translated: GHC's `$cshowsPrec` body is string
  -- plumbing that rarely matches Lean's `ToString`, and emitted data decls
  -- already `derive Repr`, which Blaster uses to print counterexamples.
  -- Translating Show would risk a *wrong* printer; skipping is sound.
  | "Show" => none
```

- [ ] **Step 4: Run to verify pass**

Run: `lake build GhcCoreToLean`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "docs: make Show-instance skip explicit (derived Repr handles printing)"
```

---

## Task 4: Design spike — user-defined classes + dictionary passing

**Files:**
- Create: `docs/superpowers/plans/<date>-userclasses-dictionaries.md` (the deliverable)

This is **not** a coding task. Today: (a) the AST has no `class` declaration node ([AST.lean](../../../GhcCoreToLean/AST.lean) has `DataDecl`/`Instance` but no `ClassDecl`); (b) dictionaries and dict-lambdas are *erased* in [Lower.lean](../../../GhcCoreToLean/Lower.lean) (`isTypeOrDictBinder`/`isTypeOrDictArg`); (c) `emitInstance` only handles the fixed classes above. Supporting arbitrary user classes means re-introducing dictionaries as Lean typeclasses end-to-end — a new subsystem. Before any step-level plan can be written, run **superpowers:brainstorming** on the design, then **superpowers:writing-plans** on the result.

- [ ] **Step 1: Inventory what Core/​the sidecar actually deliver**

Pick a fixture with a user class + instance + a polymorphic function constrained by it:

```haskell
{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module UserClass where
    import Prelude
    class Sized a where size :: a -> Int
    data Box = Box Int
    instance Sized Box where size (Box n) = n
    total :: Sized a => [a] -> Int
    total = foldr (\x acc -> size x + acc) 0
```

Run `lake build ghccoretolean && ./transpile.sh examples/haskell/UserClass.hs` and record, in the spec: how the class method `size` appears in Core (a dict selector `$dSized`/`$csize`?), how `total`'s `Sized a =>` constraint appears (a dict lambda currently erased by Lower), and whether the `decl-plugin` sidecar emits any class-declaration record (check `shim/decl-plugin/GhcDeclDump.hs`).

- [ ] **Step 2: Decide the dictionary representation** (answer in the spec, with rationale)

Resolve these design questions — they are the hard fork points:
- **Lean target:** map each GHC class to a Lean `class`, and each instance dict to a Lean `instance`? Or keep dictionaries *explicit* as `structure` values passed as ordinary arguments (closer to Core, avoids Lean instance-resolution mismatches)?
- **Dict erasure:** Lower currently erases dict binders/args. Which of those must be *un*-erased, and how to distinguish a genuine dict from the `HasCallStack` `$dIP` dict we deliberately drop ([memory](../../../.claude/projects/-Users-romainsoulat-ghcCore-to-lean/memory/transpiler-bottoms-and-builtin-ctors.md))?
- **Method dispatch:** how does a call `size x` (a dict-selector application in Core) resolve to the right Lean form under the chosen representation?
- **Superclasses / multi-param / defaults:** in scope now, or explicitly deferred?

- [ ] **Step 3: Add the AST + parser surface needed** (specified, not yet coded)

In the spec, define the new `ClassDecl` structure for [AST.lean](../../../GhcCoreToLean/AST.lean) and the `decl-plugin` JSON shape that feeds it, plus the `Parse.lean` additions — concretely enough that the follow-up plan can implement them TDD.

- [ ] **Step 4: Brainstorm → write the implementation plan**

Invoke **superpowers:brainstorming** with Steps 1–3 as input, then **superpowers:writing-plans** to produce `docs/superpowers/plans/<date>-userclasses-dictionaries.md` with bite-sized TDD tasks. That plan — not this task — implements the subsystem.

- [ ] **Step 5: Commit the spec**

```bash
git add docs/superpowers/plans/*userclasses-dictionaries.md examples/haskell/UserClass.hs
git commit -m "docs: design spike for user-defined classes + dictionary passing"
```

---

## Self-Review Notes

- **Spec coverage:** `Ord` instances → Task 2; `Show`/printing → Task 3; the finder generalization that both need → Task 1; user-defined classes + dictionaries (the large architectural item) → Task 4 spike, deliberately *not* flattened into one-line tasks alongside the table edits, per the writing-plans scope check.
- **Deferred deliberately (YAGNI until a corpus example needs it):** `Num`/`Functor`/`Applicative`/`Monad` instances for user types. Add when an annotated example requires one; each would follow the Task-2 pattern (find `$c<method>`, emit the Lean class instance) or fold into the Task-4 subsystem.
- **Type consistency:** `findClassMethod`/`emitInstance` signatures and the `Instance`/`Var`/`CoreProgram` literals match current source. ✅
- **Placeholder check:** Task 4 has no code placeholders — its steps are research questions and artifacts, which is the correct content for a design spike. ✅
