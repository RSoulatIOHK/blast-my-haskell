# M3 — Type-Class Completeness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Superclasses, default methods, same-named methods across classes, hand-written non-structural `Ord`, multi-parameter classes (spec §M3), plus builtin class constraints in signatures (`Eq a => …` → `[BEq a]`; user-approved addition). Spec: [2026-07-24-coverage-roadmap-design.md](../specs/2026-07-24-coverage-roadmap-design.md) §M3.

**Architecture:** Today's class machinery is *instance-driven Core reconstruction* (`reconstructClasses` reads `$f` dfun bodies; single-param `ClassDecl`; methodMap keyed by bare method name). Exploration verified that class SHAPES never reach the transpiler — the decl-plugin excludes class tycons ([GhcDeclDump.hs:63-70](../../../shim/decl-plugin/GhcDeclDump.hs)), class-op Ids (method and `$p` superclass selectors) are not top-level binds, and the 2026-06-20 design doc dropped superclasses for exactly this reason. So M3's enabling move is a **decl-plugin class-shape dump** (Task 1); superclasses (T5), default methods (T4), and multi-param classes (T7) build on it. Same-named methods (T2), builtin constraints (T3), and hand-written Ord (T6) are independent of the plugin work.

**Tech Stack:** Lean 4 v4.24.0; GHC 9.2.7 + cabal (decl-plugin work: `shim/decl-plugin/GhcDeclDump.hs`; rebuild via `cd shim && cabal build` AND note transpile.sh stages plugins in `.transpile-sandbox` — check how the sandbox picks up plugin rebuilds; force a re-stage if needed); Blaster.

**Branch:** `feature/m3-typeclass-completeness`, stacked on `feature/m2-records-newtypes` (PR #4).

---

## Verified starting-point facts (from exploration; trust but re-verify when touched)

1. `reconstructClasses` ([Emit.lean:587-609](../../../GhcCoreToLean/Emit.lean)) is instance-driven; classes without a local instance produce nothing (call sites emit bare → loud-ish). `ClassDecl` is single-param (`tyVar : Name`); method types recovered by `generalizeTy` head-abstraction (documented "primary correctness risk").
2. **Same-named methods are silent-wrong TODAY**: methodMap keyed by bare name, `emitVar` takes the first match by instance dump order, no diagnostic. Also `emitVar` consults methodMap BEFORE valueMap (a user method named `==` shadows the builtin map). Also `Main.lean` drops `$c/=` unconditionally — a user class declaring `/=` loses its method silently.
3. **Builtin `Eq a =>` breaks in exactly two places**: `stripClassConstraints` gate (`classNames` = user classes only) → binder mis-typed as `(x : (tyConOpaque "Eq") t)`, AND `resTyOf` strips against the unstripped type → result type shifts. Value level is already correct (dict binders/args have role `dict`, erased by Lower — verified in /tmp/transpile-BuiltinEq.json). There is NO Haskell-class→Lean-class map in Maps.lean — `[{sanitize c} …]` is emitted verbatim.
4. **Hand-written `Ord` is silently replaced today**: `ordTypes` is instance-existence-based (not `usesTagPrim`-based like Eq); all `$ccompare`/`$c<`… bodies are suppressed and `deriving Ord` takes over. The `usesTagPrim` discriminator DOES separate derived (dataToTag# present) from hand-written (absent) in both on-disk probes. M2 closed this for newtype heads only.
5. `emitInstanceUser` requires EVERY class method to have a `$c` bind — an instance relying on a default is silently dropped whole. `$dm` binds today land in userBinds unsuffixed (collision-prone). No `$dm`/`$p` occurrences in any dump — because no fixture declares defaults/superclasses, NOT because GHC doesn't emit them.
6. Multi-param: JSON/`Instance.headTypes` already list-shaped; the three single-param seams are `ClassDecl.tyVar`, `reconstructClasses` head?-only generalization, and `stripClassConstraints`' one-element pattern. `findClassMethod` compares a single first-arg type against a space-joined multi-head string — never equal → instances silently dropped.
7. Section ordering is a hard constraint (Lean instances not forward-visible): data+classes → `$c` defs → instances → user binds. Class decls are appended after data decls UNSORTED. All instance-matching keys must be computed before the resolution passes (opaque-string invariant).
8. Parameterized data types remain unsupported — multi-param and container-ish fixtures must use monomorphic data types.

## Soundness discipline

Loud-fail safe; silent-wrong never. M3 REMOVES two existing silent-wrongs (facts 2, 4) — they get refusal/correct-emission plus pins. Every new path decides loud-vs-silent explicitly; `emitInstanceUser`'s silent skip must not spread (each new `none` needs a stated justification or an eprintln path).

## Per-task loop

Edit → `lake build GhcCoreToLean` → (plugin changed? `cd shim && cabal build` + verify the sandbox re-stages: check `.transpile-sandbox` plugin artifacts' mtimes or force-clean them) → `lake build ghccoretolean` → `./transpile.sh examples/haskell/<Mod>.hs` → `lake build GhcCoreToLean.Generated.<Mod>`. Observed-names discipline as M1/M2 (fixture-first; quote spines; record negatives; hedge, never trim). `decide` ground / `blaster` quantified.

---

## File Structure

- **Modify** [shim/decl-plugin/GhcDeclDump.hs](../../../shim/decl-plugin/GhcDeclDump.hs) — class-shape dump (Task 1).
- **Modify** [GhcCoreToLean/AST.lean](../../../GhcCoreToLean/AST.lean) — `ClassDecl` v2 (tyVars list, supers, methods with hasDefault; from-plugin), keep Core-reconstruction fallback shape.
- **Modify** [GhcCoreToLean/Parse.lean](../../../GhcCoreToLean/Parse.lean) — parse `classDecls` JSON channel.
- **Modify** [GhcCoreToLean/Maps.lean](../../../GhcCoreToLean/Maps.lean) — new `classConMap` (Haskell class → Lean class/binder recipe).
- **Modify** [GhcCoreToLean/Emit.lean](../../../GhcCoreToLean/Emit.lean) — everything else.
- **Modify** [Main.lean](../../../Main.lean) — `$c/=` drop fix; validation wiring.
- **Create fixtures** `examples/haskell/`: `TwoClassesSameMethod.hs`, `BuiltinConstraints.hs`, `DefaultMethods.hs`, `SuperClass.hs`, `OrdHandwritten.hs`, `MultiParam.hs`.
- **Modify** [README.md](../../../README.md) — the §"single-parameter type classes" bullet (final task).

---

### Task 1: Decl-plugin class-shape dump (enabling foundation)

**Files:** `shim/decl-plugin/GhcDeclDump.hs`, `GhcCoreToLean/AST.lean`, `GhcCoreToLean/Parse.lean`, `GhcCoreToLean/Tests/Unit.lean`; fixture `examples/haskell/SuperClass.hs` (observation only this task).

- [ ] **Step 1: Extend the plugin.** For every class TyCon in `tcg_tcs` (via `tyConClass_maybe`), dump a `classDecls` array entry: `{name, tyVars: [String], supers: [ppType-rendered constraint heads], methods: [{name, type, hasDefault: Bool}]}` using `classTyVars`, `classSCTheta`, `classOpItems` (the `Maybe (Id, DefMethSpec)` second component ⇒ hasDefault). Keep the existing `typeDecls`/`instances` output byte-identical. Version-guard: if the GHC 9.2.7 API names differ, adapt and QUOTE the actual API used.
- [ ] **Step 2: Fixture-first observation.** Write `SuperClass.hs` (`class Sized a where size :: a -> Int; class Sized a => Container a where empty :: a; insert :: Int -> a -> a` + a data type + instances + one property). Rebuild plugin + shim, force sandbox re-stage, transpile. QUOTE: the new classDecls JSON; the dfun spine for the Container instance (does a `$p1Container`-style superclass selector reference appear? a `$cp1...`? What role?); any `$dm` if a default sneaks in. Record everything in Unit.lean.
- [ ] **Step 3: Parse + AST.** `ClassDecl` v2: `{name, tyVars: List Name, supers: List Name, methods: List {name, ty, hasDefault : Bool}}`. Reconcile with the Core-reconstruction path: `reconstructClasses` output adapts into v2 (single tyVar → [tv], no supers, hasDefault=false), and plugin-sourced decls take PRECEDENCE when both exist for a name (plugin shapes are ground truth; Core reconstruction remains the fallback for... nothing now, but keep it until Task 7 retires what's replaceable — decide and document). Guards on the parser + precedence rule.
- [ ] **Step 4: Emission unchanged this task** (single-param classes must emit exactly as before — byte-identical UserClass.lean regression). Commit.

### Task 2: Same-named methods — refuse ambiguity, fix the shadowing order

**Files:** `Emit.lean`, `Main.lean`, `Tests/Unit.lean`; fixture `TwoClassesSameMethod.hs`.

- [ ] Key methodMap entries `(method, class)` with call-site attribution: the info exists at `$c`-bind level (each `$c<m>` attributable to a dfun via `collectCMethodRefs`) — BUT call sites reference the class-op Id by bare name, so if two classes both declare `size`, call sites are genuinely ambiguous at the dump level UNLESS the selector Var carries distinguishing info (check the dump: does the reference carry a unique tied to the class-op Id? QUOTE it). If disambiguation is possible from uniques → implement it; if NOT → loud refusal listing both classes (mirroring `localImportCollisionError`), which is still strictly better than today's silent first-match. Report which branch reality forced.
- [ ] Fix `emitVar` order: methodMap must not shadow `valueMap` for operator names — decide the precedence (builtin operators win? or refuse a user method named `==`?) and pin it.
- [ ] Fix the `Main.lean` unconditional `$c/=` drop: only drop when the type's Eq image is the builtin path (or match `$c/=` only when an Eq instance for that head exists — design minimally, pin behavior for a user class declaring `/=`).
- [ ] Fixture: two classes with the same method name + instances + call sites; expected outcome per the branch taken above. Commit.

### Task 3: Builtin class constraints in signatures

**Files:** `Maps.lean` (`classConMap`), `Emit.lean` (`stripClassConstraints`, `resTyOf`, `emitDefHeader` threading), `Tests/Unit.lean`; fixture `BuiltinConstraints.hs`.

- [ ] `Maps.classConMap : Name → Option (String → String)` (or `Name → Option String` binder-template): `"Eq" ↦ [BEq t]`; `"Ord" ↦` DESIGN DECISION — the ops emit as `decide (a < b)` (Prop-based `LT`/`LE`), so the binder set must make those elaborate: candidate `[Ord t] [BEq t]` + `leOfOrd/ltOfOrd`-style local instances, or `[LT t] [LE t] [DecidableEq t] [DecidableRel ...]` — PROBE in a scratch Lean file which minimal binder set makes `fun (x y : t) => decide (x < y)` + `min`/`max`/`compare` elaborate, and pin the choice; `"Num" ↦` attempt `[Add t] [Sub t] [Mul t] [Neg t] [OfNat t 0] [OfNat t 1]` in the same probe — if it works, map it; if it turns ugly, leave `Num` unmapped (still loud) and record the deferral.
- [ ] Widen `stripClassConstraints`: gate on `classNames ∪ classConMap-mapped`, emit the mapped binder for builtins and `[{C} {t}]` for user classes (unchanged). Fix `resTyOf` to strip with the SAME widened gate (fact 3's second defect).
- [ ] Fixture: `allSame :: Eq a => a -> a -> Bool`, `maxG :: Ord a => [a] -> a` (this also finally exercises M1's `[Inhabited t]` + partial-maximum path e2e! — expect `[Ord t] [Inhabited t]`-style headers), a Num one if mapped. Quantified blaster properties at Int instantiation + polymorphic compile checks. Commit.

### Task 4: Default methods

**Files:** `Emit.lean`, `Main.lean`, `Tests/Unit.lean`; fixture `DefaultMethods.hs`.

- [ ] Fixture-first: `class Greet a where name :: a -> Int; greet :: a -> Int; greet x = name x + 1` + one instance overriding, one relying on the default. QUOTE the `$dm` spines and how the relying instance's dfun references `$dmgreet`.
- [ ] Emission: class body gets `greet : … := fun x => …` defaults (translate the `$dm` bind body; it references the class dict — check how Lower's dict erasure leaves it and whether the class-param methods resolve via the instance-implicit in scope inside a Lean class default — probe the Lean syntax in a scratch file first).
- [ ] `emitInstanceUser`: per-method fallback — a method with `hasDefault` and no `$c` bind is OMITTED from the instance (Lean fills it); a method without default and without `$c` bind stays a LOUD skip but now with an eprintln naming the instance and method (kill the silent skip). `$dm` binds excluded from userBinds. Commit.

### Task 5: Superclasses

**Files:** `Emit.lean`, `Tests/Unit.lean`; fixture `SuperClass.hs` (from Task 1, now activated).

- [ ] Emission: user-class superclass → `class Container (a : Type) extends Sized a where …`; builtin superclass (`Eq a => class C a`) → instance-implicit field `[BEq a]` inside the class (via classConMap). Probe Lean-side first: does `extends` + the dfun-derived instance emission compose (instance of Container must provide the parent — how does Lean want it? `instance : Container T where toSized := …`? or does the parent instance in scope suffice? PROBE, then design emitInstanceUser's superclass handling to match).
- [ ] Core side: whatever `$p`/`$cp` selector references Task 1's observation found inside dfun bodies get handled per-observation (likely: superclass-dict extraction erased like dicts; method calls through them resolve via methodMap + Lean instance inference). Class-decl ordering: sort classDecls by superclass dependency (reuse the `sortDataDecls` idiom; classes after data decls).
- [ ] e2e: SuperClass.hs properties verify. Commit.

### Task 6: Hand-written non-structural Ord

**Files:** `Emit.lean`, `Tests/Unit.lean`; fixture `OrdHandwritten.hs` (DATA-headed — newtype heads are refused by M2).

- [ ] Replace instance-existence `ordTypes` with `derivedOrdTypes` via `usesTagPrim` over `$ccompare` (mirror `derivedEqTypes`); hand-written Ord emits `instance : Ord T where compare := <$ccompare ref>` + the LE/LT/Min/Max companions (today only emitted in `emitDataDecl` for derived) — mind the forward-visibility ordering (fact 7) and compute all keys pre-resolution-passes.
- [ ] The "small enum indistinguishable" caveat: a derived Ord on a small enum MAY lack tag primops (the old comment's claim) — probe it (`data T = A | B deriving Ord`, check the dump). If the heuristic misclassifies derived-as-handwritten, the emitted instance still computes the same order (derived compare body IS the order) — argue or refute soundness of the misclassification direction explicitly; the reverse direction (hand-written classified derived = today's silent-wrong) must be impossible under the new scan. Pin both directions.
- [ ] Fixture: cross-multiply-style Ord on a 2-field data ratio type + ordering properties (`∀ …, lt (mk 1 2) (mk 2 3) = …` style with preconditions) verified by blaster. This closes the README's "hand-written non-structural Ord would be modeled structurally" limitation. Commit.

### Task 7: Multi-parameter classes

**Files:** `Emit.lean`, `Tests/Unit.lean`; fixture `MultiParam.hs` (monomorphic data types only — fact 8).

- [ ] `emitClassDecl` over `tyVars` list; `stripClassConstraints` multi-var pattern (`[C a b]`); `reconstructClasses`/`generalizeTy` for multi-head (generalize each head type to its own tyvar — or, now that plugin shapes exist (Task 1), source arity+tyvars from the plugin and use Core only for method-body refs — prefer the plugin route, document); `findClassMethod` key fix (match against the full head; the space-joined string comparison needs a per-head structural match).
- [ ] Fixture: `class Convert a b where conv :: a -> b` + two instances + call sites + properties. Explicitly out of scope (README): functional dependencies, overlapping instances. Commit.

### Task 8: README + full regression + gate

- [ ] README: rewrite the type-class bullet (single-param restriction lifted; enumerate what IS supported now; new limitations: fundeps, overlap, methods not mentioning class params (still — unless Task 1's shapes fixed recovery; verify and state), Num-constraint status per Task 3's outcome).
- [ ] Full-corpus collect-don't-break regression (M1/M2 loop; NewtypeInstances expected-fail; UserClass known-red unless user fixed it — CHECK first; user's uncommitted edits tested-not-committed).
- [ ] Milestone gate: final whole-branch review subagent → stacked PR → user checkpoint.

---

## Self-review notes

- Spec §M3 items all covered: superclasses T5, defaults T4, same-named T2, hand-written Ord T6, MPTC T7; approved addition (builtin constraints) T3; enabling plugin work T1.
- T1 precedes T4/T5/T7 (shape-dependent); T2/T3/T6 are independent and can reorder if a task blocks.
- Fixture-first observation steps carry QUOTE-the-spine requirements and explicit branch decisions (T2's disambiguate-vs-refuse; T6's heuristic-direction argument) rather than assumed mechanisms.
- Plugin work is the highest-risk item (GHC 9.2.7 API, sandbox staging) — T1 Step 1 has the adapt-and-quote rule; if the plugin route fails entirely, T4/T5/T7 fall back to Core-only observation and the plan must be revised (stop and escalate, don't improvise).
