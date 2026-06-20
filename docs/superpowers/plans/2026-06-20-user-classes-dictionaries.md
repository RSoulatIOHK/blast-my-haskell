# User-defined Type Classes (from-Core) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transpile single-parameter user-defined type classes (class decl, instances, methods, and `C a =>`-constrained functions) to idiomatic Lean classes, reconstructed entirely from the existing Core dump — no GHC-plugin changes.

**Architecture:** Reconstruct a `ClassDecl` from the parsed `Program` (instance dict-builders reference their `$c<method>` binds; method signatures generalized from those binds). Emit `class C (a : Type) where …` in the data block, then `$c` method defs, then `instance : C T where …`, then user binds — this order matters because Lean instances/classes are NOT forward-visible. Rewrite bare selector uses (`size` → `Sized.size`) and constrained-function headers (`Sized a =>` → `[Sized a]`).

**Tech Stack:** Lean 4 v4.24.0, `lake`; GHC 9.2.7 for end-to-end transpiles. Spec: `docs/superpowers/specs/2026-06-20-user-classes-dictionaries-design.md`. Revert baseline: commit `11f8531`.

**Verified data shapes (from `/tmp/transpile-UserClass.json`):**
- dfun `$fSizedBox` body references exactly `["$csize"]` (its methods).
- `$csize` binder type is a function `Box → Int` (`{tag, arg, res}` ⇒ `.tyFun`).
- `total` body references `$dSized` (dict arg, role `.dict`) and `size` (bare selector).
- Top-level binds also include Typeable junk: `$krep`, `$tc'Box`, `$tc'C:Sized`, `$tcBox`, `$tcSized`, `$trModule` — these must be filtered out of emission.

**Per-task loop:** edit → `lake build GhcCoreToLean` (runs `#guard`s) → for e2e: `lake build ghccoretolean && ./transpile.sh examples/haskell/UserClass.hs && lake build GhcCoreToLean.Generated.UserClass`.

**Established conventions to follow:** `#guard` unit tests in `GhcCoreToLean/Tests/Unit.lean` (append inside `namespace GhcCoreToLean.Tests ... end`); qualified-name-only mappings; definition-focused e2e fixtures (proofs are the user's). Commit trailer: `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.

---

## File Structure

- **Modify** `GhcCoreToLean/AST.lean` — add `ClassMethod`, `ClassDecl`.
- **Modify** `GhcCoreToLean/Emit.lean` — reconstruction pass (`reconstructClasses`), `emitClassDecl`, generalized `emitInstance` for user classes, selector rewrite in `emitVar`, constrained-header logic, `emitFullProgram` ordering. (Reconstruction could be a new module, but Emit already owns instance/data emission and the helpers it needs; keep it here to avoid a new import cycle, consistent with the existing file's scope.)
- **Modify** `GhcCoreToLean/Tests/Unit.lean` — `#guard`s per task.
- **Use** `examples/haskell/UserClass.hs` (already committed) — e2e fixture.

---

## Task 1: AST types `ClassMethod` / `ClassDecl`

**Files:** Modify `GhcCoreToLean/AST.lean`; Test: `GhcCoreToLean/Tests/Unit.lean`

- [ ] **Step 1: Write the failing guard** — append to `Unit.lean`:

```lean
-- Dict Task 1: ClassDecl / ClassMethod AST types exist and hold the shape.
def sizedClass : ClassDecl :=
  { name := "Sized", tyVar := "a",
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
#guard sizedClass.name == "Sized"
#guard sizedClass.methods.length == 1
#guard (sizedClass.methods.head!).name == "size"
```

- [ ] **Step 2: Run → FAIL** (`lake build GhcCoreToLean`) — `unknown identifier ClassDecl`.

- [ ] **Step 3: Implement** — in `GhcCoreToLean/AST.lean`, add before `structure Program` (near `DataDecl`/`Instance`):

```lean
structure ClassMethod where
  name : Name
  ty   : GHCType   -- the *generalized* method type, e.g. `a → Int`
deriving Repr, Inhabited

structure ClassDecl where
  name    : Name
  tyVar   : Name           -- the class's type parameter, e.g. "a"
  methods : List ClassMethod
deriving Repr, Inhabited
```

- [ ] **Step 4: Run → PASS** (`lake build GhcCoreToLean`).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/AST.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(classes): add ClassDecl/ClassMethod AST types

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: Reconstruct classes from binds + instances

**Files:** Modify `GhcCoreToLean/Emit.lean`; Test: `GhcCoreToLean/Tests/Unit.lean`

Build `reconstructClasses : CoreProgram → List Instance → List ClassDecl × List (Name × Name)` where the second component is the `(method-name, class-name)` map (e.g. `("size","Sized")`). Algorithm (grounded in verified data):
- For each `Instance i`, find the bind named `i.dfunName` (e.g. `$fSizedBox`); collect the names of `$c…`-prefixed `Var`s referenced anywhere in its rhs → that instance's method bindings.
- For each such `$c<m>` binding, the method name is `<m>` (strip the `$c` prefix); its **generalized** signature is the `$c<m>` binding's own type with the instance head type replaced by the class tyVar `a` (Task 2b).
- Group by `i.className` → one `ClassDecl` per class (dedup methods by name).

Helpers needed (define near `firstValArgTy`):

- [ ] **Step 1: Write the failing guards** — append to `Unit.lean`:

```lean
-- Dict Task 2: reconstruct ClassDecl + method→class map from binds + instances.
def csizeBind : Bind :=
  .nonRec {name := "$csize", unique := 90,
           ty := .tyFun (.tyCon "Box" []) (.tyCon "Int" []), role := .id}
          (.lam {name := "b", unique := 1, ty := .tyCon "Box" [], role := .id}
                (.lit (.litInt 0)))
def dfunBind : Bind :=
  .nonRec {name := "$fSizedBox", unique := 91, ty := .tyCon "Sized" [.tyCon "Box" []], role := .id}
          (.var {name := "$csize", unique := 90, ty := .tyFun (.tyCon "Box" []) (.tyCon "Int" []), role := .id})
def sizedInst : Instance :=
  {className := "Sized", headTypes := [.tyCon "Box" []], dfunName := "$fSizedBox", dfunUnique := 91}
def reconRes := reconstructClasses [csizeBind, dfunBind] [sizedInst]
#guard reconRes.1.length == 1
#guard (reconRes.1.head!).name == "Sized"
#guard (reconRes.1.head!).methods.map (·.name) == ["size"]
#guard reconRes.2 == [("size", "Sized")]
-- generalized method sig: Box head replaced by tyVar "a" → (a → Int)
#guard emitType (reconRes.1.head!).methods.head!.ty == emitType (.tyFun (.tyVar "a") (.tyCon "Int" []))
```

- [ ] **Step 2: Run → FAIL** (`unknown identifier reconstructClasses`).

- [ ] **Step 3: Implement** — in `GhcCoreToLean/Emit.lean`, add (after `firstValArgTy`, before `findClassMethod`):

```lean
/-- Names of `$c…` class-method `Var`s referenced anywhere in an expression. -/
private partial def collectCMethodRefs : Expr → List Name
  | .var v       => if v.name.startsWith "$c" then [v.name] else []
  | .app f a     => collectCMethodRefs f ++ collectCMethodRefs a
  | .lam _ b     => collectCMethodRefs b
  | .let_ bnd b  =>
    (match bnd with
     | .nonRec _ e => collectCMethodRefs e
     | .rec_ ps    => ps.flatMap (fun p => collectCMethodRefs p.2))
      ++ collectCMethodRefs b
  | .case_ s _ _ alts => collectCMethodRefs s ++ alts.flatMap (fun (.mk _ _ r) => collectCMethodRefs r)
  | .cast e      => collectCMethodRefs e
  | .tick e      => collectCMethodRefs e
  | _            => []

/-- Look up a top-level binding by name. -/
private def findBind (binds : CoreProgram) (n : Name) : Option (Var × Expr) :=
  binds.findSome? fun b => match b with
    | .nonRec v e => if v.name == n then some (v, e) else none
    | .rec_ pairs => pairs.find? (fun (v, _) => v.name == n)

/-- Replace every `tyCon headName …` occurrence with `tyVar tv` (generalize an
    instance-specialized method type back to the class-parameter form). -/
private partial def generalizeTy (headName tv : Name) : GHCType → GHCType
  | .tyCon n args => if n == headName && args.isEmpty then .tyVar tv
                     else .tyCon n (args.map (generalizeTy headName tv))
  | .tyApp f x    => .tyApp (generalizeTy headName tv f) (generalizeTy headName tv x)
  | .tyFun a r    => .tyFun (generalizeTy headName tv a) (generalizeTy headName tv r)
  | .forAll v b   => .forAll v (generalizeTy headName tv b)
  | t             => t

/-- Reconstruct `ClassDecl`s + a `(method, class)` map from the program's
    instance dict-builders (which reference their `$c<method>` bindings) and
    the `$c<method>` binding types (generalized to the class parameter). -/
def reconstructClasses (binds : CoreProgram) (insts : List Instance)
    : List ClassDecl × List (Name × Name) :=
  let tv := "a"
  let perInstance (i : Instance) : Option (ClassDecl × List (Name × Name)) := do
    let (_, dfunRhs) ← findBind binds i.dfunName
    let headName ← match i.headTypes.head? with | some (.tyCon n _) => some n | _ => none
    let cmethods := (collectCMethodRefs dfunRhs).eraseDups
    let methods := cmethods.filterMap fun cm => do
      let (mv, _) ← findBind binds cm
      let mname := cm.drop 2   -- strip "$c"
      some ({ name := mname, ty := generalizeTy headName tv mv.ty } : ClassMethod)
    let pairs := methods.map (fun m => (m.name, i.className))
    some ({ name := i.className, tyVar := tv, methods }, pairs)
  let results := insts.filterMap perInstance
  -- Dedup classes by name (multiple instances of one class → merge methods).
  let classes := results.foldl (init := ([] : List ClassDecl)) fun acc (cd, _) =>
    if acc.any (·.name == cd.name) then acc else acc ++ [cd]
  let methodMap := (results.flatMap (·.2)).eraseDups
  (classes, methodMap)
```

> NOTE on `.drop 2`: `"$csize".drop 2 == "size"` (drops `$c`). `String.drop` exists in Lean v4.24. If the dump ever suffixes methods (`$csize_123`), `mname` would be wrong — verify against the Step-2-of-Task-7 e2e output and trim a trailing `_<digits>` if present (none in the verified `UserClass` dump).

- [ ] **Step 4: Run → PASS** (`lake build GhcCoreToLean`).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(classes): reconstruct ClassDecl + method→class map from Core

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: `emitClassDecl`

**Files:** Modify `GhcCoreToLean/Emit.lean`; Test: `GhcCoreToLean/Tests/Unit.lean`

- [ ] **Step 1: Failing guard** — append:

```lean
-- Dict Task 3: emit a Lean `class` from a ClassDecl.
#guard emitClassDecl sizedClass ==
  "class Sized (a : Type) where\n  size : (a → Int)"
```

(`sizedClass` is defined in the Task 1 guards.)

- [ ] **Step 2: Run → FAIL.**

- [ ] **Step 3: Implement** — in `Emit.lean`, near `emitDataDecl`:

```lean
/-- Emit a single-parameter user class as a Lean `class`. -/
def emitClassDecl (c : ClassDecl) : String :=
  let methodLines := c.methods.map fun m =>
    s!"  {sanitize m.name} : {emitType m.ty}"
  s!"class {sanitize c.name} ({tyVarId c.tyVar} : Type) where\n" ++
    String.intercalate "\n" methodLines
```

> `emitType (.tyVar "a")` yields `tyVarId "a"` = `"a"`. The guard's expected string uses `(a → Int)` because `emitType` parenthesizes function types. Confirm the exact parenthesization in Step 2's failure message and match the guard to it (adjust the expected string, not the emitter, if `emitType` differs).

- [ ] **Step 4: Run → PASS.**

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(classes): emit Lean class from ClassDecl

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 4: Selector rewrite in `emitVar`

**Files:** Modify `GhcCoreToLean/Emit.lean`; Test: `GhcCoreToLean/Tests/Unit.lean`

`emitVar` must rewrite a bare class-method selector (`size`) to `Class.method` (`Sized.size`). Thread the method→class map through. Current signature: `emitVar (topNames : List Name) (v : Var) : String`. Add the map as a parameter and thread it through `emitExpr`/`emitAlt`/`emitLet`/`emitBind`/`emitProgram*`.

To avoid a large signature churn, store the map in a `private` parameter threaded ONLY where needed: add `(methodMap : List (Name × Name))` as the FIRST parameter of `emitVar`, `emitExpr`, `emitAlt`, `emitLet` (the mutual block), `emitBind`, `emitProgram`, `emitProgramWith`. Update all call sites.

- [ ] **Step 1: Failing guard** — append:

```lean
-- Dict Task 4: a bare class-method selector emits `Class.method`.
#guard emitVar [("size","Sized")] [] {name := "size", unique := 7, ty := .tyFun (.tyVar "a") (.tyCon "Int" []), role := .id} == "Sized.size"
-- a non-method bare name is unaffected.
#guard emitVar [("size","Sized")] [] {name := "other", unique := 8, ty := .tyCon "Int" [], role := .id} == "other_8"
```

- [ ] **Step 2: Run → FAIL** (arity mismatch / wrong output).

- [ ] **Step 3: Implement** — change `emitVar`:

```lean
def emitVar (methodMap : List (Name × Name)) (topNames : List Name) (v : Var) : String :=
  match methodMap.find? (·.1 == v.name) with
  | some (_, cls) => s!"{sanitize cls}.{sanitize v.name}"
  | none =>
  match valueMap v.name with
  | some lean => lean
  | none      =>
    match dataConMap v.name with
    | some lean => lean
    | none      => refId topNames v
```

Then thread `methodMap` as the new first parameter through `emitExpr`, `emitAlt`, `emitLet` (mutual block), `emitBind`, `emitProgram`, `emitProgramWith`, updating every call site (the compiler will flag each until consistent). At the `emitExpr` `.var` case: `emitVar methodMap top v`.

> This is a mechanical signature-threading change touching many call sites; let the build errors guide you until green. Keep `methodMap` FIRST so the diff is uniform.

- [ ] **Step 4: Run → PASS** (`lake build GhcCoreToLean` — all existing guards still pass with `[]` method maps where callers don't have one).

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(classes): rewrite class-method selectors to Class.method in emitVar

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 5: Generalized `emitInstance` for user classes

**Files:** Modify `GhcCoreToLean/Emit.lean`; Test: `GhcCoreToLean/Tests/Unit.lean`

Extend `emitInstance` so a class that is NOT a built-in (Eq/Ord/Show) but IS a reconstructed user class emits `instance : C T where m₁ := <$cm₁ ref> …`. Pass the reconstructed `List ClassDecl` so `emitInstance` knows the method set + field names.

- [ ] **Step 1: Failing guard** — append:

```lean
-- Dict Task 5: a user-class instance emits `instance : C T where m := <ref>`.
#guard (emitInstanceUser [sizedClass] [csizeBind, dfunBind] sizedInst).getD ""
       |>.splitOn "instance : Sized (GHCCore.tyConOpaque \"Box\") where" |>.length == 2
#guard (emitInstanceUser [sizedClass] [csizeBind, dfunBind] sizedInst).getD ""
       |>.splitOn "size := " |>.length == 2
```

- [ ] **Step 2: Run → FAIL.**

- [ ] **Step 3: Implement** — add a helper `emitInstanceUser` and call it from `emitInstance`'s `_` arm:

```lean
/-- Emit a user-class instance: for each class method, find the matching
    `$c<method>` binding for this instance's head type and wire it as a field. -/
def emitInstanceUser (classes : List ClassDecl) (binds : CoreProgram) (i : Instance) : Option String := do
  let cd ← classes.find? (·.name == i.className)
  let tyStr := i.headTypes.map emitType |> String.intercalate " "
  let fields := cd.methods.filterMap fun m =>
    match findClassMethod binds ("$c" ++ m.name) tyStr with
    | some ref => some s!"  {sanitize m.name} := {ref}"
    | none     => none
  if fields.length == cd.methods.length then
    some s!"instance : {sanitize i.className} {tyStr} where\n" ++ String.intercalate "\n" fields
  else none   -- a method we couldn't resolve → skip rather than emit broken
```

Then in `emitInstance`'s final arm, pass `classes` (add it as a parameter to `emitInstance`):
change `emitInstance (derivedEq : List String) (binds) (i)` →
`emitInstance (classes : List ClassDecl) (derivedEq : List String) (binds) (i)` and replace `| _ => none` with `| _ => emitInstanceUser classes binds i`. Update the call site in `emitFullProgram` (Task 7).

> `findClassMethod` matches `$c<method>` by first-value-arg type == head string; the existing helper already does this. For `$csize` the head is `Box` → `(GHCCore.tyConOpaque "Box")`, matching `tyStr`.

- [ ] **Step 4: Run → PASS.**

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(classes): emit user-class instances (N methods)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 6: Constrained-function header (`C a =>` → `[C a]`, erase dict args)

**Files:** Modify `GhcCoreToLean/Emit.lean`; Test: `GhcCoreToLean/Tests/Unit.lean`

A function like `total :: Sized a => [a] -> Int` has a Core type `∀ a. Sized a → [a] → Int`. Today `emitDefHeader` reads arg types from the signature and emits the `Sized` dict as `(GHCCore.tyConOpaque "Sized") …` — both as a leaked arg type and missing the instance-implicit binder. Fix `emitDefHeader` to:
1. detect signature arg positions whose type is a class constraint `tyCon C [tyVar …]` where `C` is a reconstructed class, emit them as instance-implicit `[C a]` binders (not value args),
2. skip those positions when zipping term binders to arg types.

The dict term-binder is already erased by `Lower` (`isTypeOrDictBinder` for `.dict` role), so the term lambda has no dict param; only the *type* carries it. The header must therefore consume the dict arrow from the signature without consuming a term binder.

- [ ] **Step 1: Failing guard** — append (drives the header through `emitBind`):

```lean
-- Dict Task 6: a `C a =>`-constrained def emits `[C a]` and no leaked dict arg.
def totalBind : Bind :=
  .nonRec
    {name := "total", unique := 70,
     ty := .forAll "a" (.tyFun (.tyCon "Sized" [.tyVar "a"])
            (.tyFun (.tyCon "List" [.tyVar "a"]) (.tyCon "Int" []))),
     role := .id}
    (.lam {name := "xs", unique := 71, ty := .tyCon "List" [.tyVar "a"], role := .id}
          (.lit (.litInt 0)))
#guard (emitBind [] ["Sized"] totalBind).splitOn "[Sized a]" |>.length == 2
#guard (emitBind [] ["Sized"] totalBind).splitOn "tyConOpaque \"Sized\"" |>.length == 1
```

(Here `emitBind`'s new params are `methodMap` (Task 4, `[]` here) and a new `classNames : List Name` (`["Sized"]`).)

- [ ] **Step 2: Run → FAIL.**

- [ ] **Step 3: Implement** — thread `classNames : List Name` into `emitBind`/`emitDefHeader`. In `emitDefHeader`, add a constraint-collection pass over the signature: walk the `tyFun`/`forAll` spine; an arg whose type is `.tyCon C [.tyVar t]` with `C ∈ classNames` becomes a constraint `[C t]` (emit `[{sanitize C} {tyVarId t}]`) and is dropped from `headerArgTys`. Concretely add:

```lean
/-- Split a def signature into (class-constraint binders, remaining value-arg
    types consumed by the term binders). Forall nodes contribute their tyvar
    implicit (handled elsewhere) and are skipped here. -/
private partial def splitConstraints (classNames : List Name) : GHCType → List String × GHCType
  | .forAll _ b => splitConstraints classNames b
  | .tyFun (.tyCon c [.tyVar t]) r =>
    if classNames.contains c then
      let (cs, rest) := splitConstraints classNames r
      (s!"[{sanitize c} {tyVarId t}]" :: cs, rest)
    else (([], .tyFun (.tyCon c [.tyVar t]) r))   -- a real value arg; stop peeling constraints
  | t => ([], t)
```

In `emitDefHeader`, after computing `tyvars`/`implStr`, call `splitConstraints classNames v.ty` to get `(constraintBinders, _)`; insert `constraintBinders` into the binder list (after the `{t : Type}` implicits, before value args); and make `headerArgTys` start from the constraint-stripped tail so dict args aren't emitted as value params. (Term binders already exclude the erased dict, so the arg/binder zip stays aligned once constraints are stripped from the type.)

> This is the most compiler-iterative task — the exact interaction between `peelLams` (term binders), `headerArgTys` (signature arg types), and constraint-stripping must keep them aligned. The two guards pin the observable contract (`[Sized a]` present, no `tyConOpaque "Sized"`). Iterate against them + the Task-7 e2e. If alignment proves fragile, an acceptable fallback is to strip leading class-constraint arrows from `v.ty` BEFORE `peelLams`/`headerArgTys` run and prepend the `[C a]` binders — document whichever you do.

- [ ] **Step 4: Run → PASS.**

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean GhcCoreToLean/Tests/Unit.lean
git commit -m "feat(classes): emit [C a] instance-implicit for constrained defs; erase dict args

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 7: Wire `emitFullProgram` (ordering) + end-to-end

**Files:** Modify `GhcCoreToLean/Emit.lean`; Test: end-to-end on `examples/haskell/UserClass.hs`

Compose everything with the forward-visibility-safe ordering: data+class block → `$c` method defs → instances → user binds. Also filter out Typeable junk binds.

- [ ] **Step 1: Implement `emitFullProgram` changes.** In `emitFullProgram`:
  1. `let (classes, methodMap) := reconstructClasses p.binds p.instances`
  2. `let classNames := classes.map (·.name)`
  3. Reconstruct class decls into the data block: `classBlock := String.intercalate "\n\n" (classes.map emitClassDecl)`; prepend to `dataBlock`.
  4. Partition `keptBinds` (after the existing derived-method suppression) into:
     - `methodDefs` — binds whose name `startsWith "$c"`,
     - `junk` — binds whose name `∈` Typeable set (`startsWith "$tc"` || `startsWith "$tr"` || `startsWith "$kr"` || `startsWith "$f"`) — DROP these from emission (the `$f` dfuns and `$tc`/`$tr`/`$kr` metadata have no Lean image; instances are emitted separately),
     - `userBinds` — the rest.
  5. Emit order in the body: `methodDefs` (via `emitProgramWith methodMap … `) then `insts` then `userBinds`. (Classes are in the data block, first.)
  6. `insts := p.instances.filterMap (emitInstance classes methodMap-not-needed derivedEq p.binds i)` — pass `classes` (Task 5) so user-class instances emit; keep Eq/Ord handling.
  7. Thread `methodMap` and `classNames` into all `emitProgramWith`/`emitBind` calls (Tasks 4, 6).

> Filtering `$f` dfuns: the instance dict-builders (`$fSizedBox`) must NOT be emitted as defs (they reference the class dict constructor `C:Sized` which has no Lean image); the `instance` blocks replace them. Confirm no surviving reference to a dropped `$f`/`$tc` name in the generated output.

- [ ] **Step 2: End-to-end build**

Run: `lake build ghccoretolean && ./transpile.sh examples/haskell/UserClass.hs && lake build GhcCoreToLean.Generated.UserClass`
Expected: PASS. Inspect `GhcCoreToLean/Generated/UserClass.lean`:
- `class Sized (a : Type) where size : a → Int` (in data block, before `total`),
- `instance : Sized Box where size := …` (before `boxTotal`),
- `def total {a : Type} [Sized a] (…) := …` using `Sized.size`,
- `def boxTotal : List Box → Int := total`,
- NO `(GHCCore.tyConOpaque "Sized")`, NO dangling `size_…`, NO emitted `$fSizedBox`/`$tcSized`/`$krep`.

Record the generated `total`/`Sized`/instance lines in the report. (Definition-focused — no `[lean|]` proof; per project convention.)

- [ ] **Step 3: Regression** — `lake build GhcCoreToLean` (all prior `#guard`s + Spike examples still pass), and re-transpile `OrdInstance.hs` + `Ratio.hs` to confirm the ordering/junk-filter changes didn't break built-in instances (Coin compiles; Ratio's hand-written BEq still emitted).

- [ ] **Step 4: Commit**

```bash
git add GhcCoreToLean/Emit.lean
git commit -m "feat(classes): wire class/instance/selector emission with forward-safe ordering

End-to-end: UserClass.hs (class Sized + instance Box + constrained total) compiles.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 8: README coverage note

**Files:** Modify `README.md`

- [ ] **Step 1:** In the Limitations section, update the "Not yet supported" bullet to reflect that single-parameter user classes now work:

```markdown
- User-defined single-parameter type classes now transpile: `class C a where …`
  → Lean `class`, instances → Lean `instance`, `C a =>` constraints →
  instance-implicit `[C a]`, method calls → `C.method`. Not yet: superclasses,
  multi-parameter classes, default methods, and same-named methods across
  classes.
```

- [ ] **Step 2: Commit**

```bash
git add README.md
git commit -m "docs: note single-parameter user-class support

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Self-Review Notes

- **Spec coverage:** ClassDecl/reconstruction → Tasks 1–2; emit class → 3; selector rewrite → 4; instances → 5; `[C a]` constraint + dict erasure → 6; ordering + junk filter + e2e → 7; docs → 8. All spec sections covered. ✅
- **Type consistency:** `reconstructClasses : CoreProgram → List Instance → List ClassDecl × List (Name × Name)`; `methodMap : List (Name × Name)`; `emitVar` / `emitExpr` / `emitBind` gain `methodMap` (first) and `emitBind`/`emitDefHeader` gain `classNames`; `emitInstance` gains `classes : List ClassDecl`. These signatures are used consistently across Tasks 4–7. ✅
- **Compiler-iteration flags (not placeholders — each has a pinning test + fallback):** method-name `$c`-strip suffix edge (Task 2), `emitType` parenthesization (Task 3), constraint/term-binder alignment (Task 6). These are genuine elaboration details the executor confirms against `lake build` + the e2e; the observable contracts are pinned by guards.
- **Ordering is load-bearing** (Lean instances not forward-visible): classes in data block; method defs before instances before user binds (Task 7). Verified necessary by the Tier-3 Ord work.
