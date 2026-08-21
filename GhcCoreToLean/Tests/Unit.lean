import GhcCoreToLean.Maps
import GhcCoreToLean.Emit
import GhcCoreToLean.AST
import GhcCoreToLean.Parse
import GhcCoreToLean.Lower
import GhcCoreToLean.Runtime

namespace GhcCoreToLean.Tests
open GHCCore GHCCore.Maps GHCCore.Emit

-- Sentinel: proves the harness builds and `#guard` failures break the build.
#guard valueMap "GHC.Base.id" == some "id"

-- Task 1: total list/Prelude combinators
#guard valueMap "GHC.Base.++"        == some "List.append"
#guard valueMap "++"                 == some "List.append"
#guard valueMap "GHC.Base.map"       == some "List.map"
#guard valueMap "GHC.List.filter"    == some "List.filter"
#guard valueMap "GHC.List.length"    == some "(fun xs => (List.length xs : Int))"
#guard valueMap "GHC.List.reverse"   == some "List.reverse"
#guard valueMap "GHC.List.null"      == some "List.isEmpty"
#guard valueMap "GHC.List.foldr"     == some "(fun f z xs => List.foldr f z xs)"
#guard valueMap "GHC.List.foldl"     == some "(fun f z xs => List.foldl f z xs)"
#guard valueMap "GHC.Classes.&&"     == some "(· && ·)"
#guard valueMap "&&"                 == some "(· && ·)"
#guard valueMap "GHC.Classes.||"     == some "(· || ·)"
#guard valueMap "GHC.Classes.not"    == some "not"
#guard valueMap "GHC.Base.const"     == some "(Function.const _)"
#guard valueMap "GHC.Base.flip"      == some "(fun f a b => f b a)"
#guard valueMap "GHC.Base.$"         == some "(fun f x => f x)"
#guard valueMap "GHC.Base.otherwise" == some "true"

-- Task 2: tuples. Names observed from Generated/TupleBasics.lean (Step 2):
--   type tycon       : "(,)"            (inside GHCCore.tyConOpaque)
--   value-pos ctor   : "GHC.Tuple.(,)"
--   pattern-pos ctor : "(,)"
--   fst / snd        : "Data.Tuple.fst" / "Data.Tuple.snd"
#guard typeConMap "(,)"  ["Int", "Int"]        == some "(Int × Int)"
#guard typeConMap "(,,)" ["Int", "Int", "Int"] == some "(Int × Int × Int)"
-- 2-tuple construction only (see report): bare + qualified resolve to Prod.mk.
#guard dataConMap "(,)"           == some "Prod.mk"
#guard dataConMap "GHC.Tuple.(,)" == some "Prod.mk"
-- 2-tuple positional pattern (pattern-position ctor name is the bare "(,)").
#guard emitAltPattern (.dataCon "(,)")
         [ {name := "x", unique := 1, ty := .tyCon "Int" [], role := .id},
           {name := "y", unique := 2, ty := .tyCon "Int" [], role := .id} ]
       == "(x_1, y_2)"
#guard valueMap "Data.Tuple.fst" == some "Prod.fst"
#guard valueMap "Data.Tuple.snd" == some "Prod.snd"

-- Task 3: Num/Integral/Ord completion. LHS names confirmed via Generated/NumOrd.lean:
--   divMod/quotRem/gcd/lcm  : GHC.Real.*
--   signum                  : GHC.Num.signum
--   compare                 : GHC.Classes.compare
--   Ordering type           : "Ordering" (inside GHCCore.tyConOpaque)
--   LT/EQ/GT constructors   : GHC.Types.LT / GHC.Types.EQ / GHC.Types.GT
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
-- Task 3: behavioral locks on the error-prone Int semantics (sign of remainder
-- on negative operands; signum). String guards above can't catch a wrong
-- truncate-vs-floor direction; these do.
#guard (Int.fdiv (-7) 2, Int.fmod (-7) 2) == (-4, 1)    -- div/mod: floor
#guard (Int.tdiv (-7) 2, Int.tmod (-7) 2) == (-3, -1)   -- quot/rem: truncate
#guard ((fun a b => (Int.fdiv a b, Int.fmod a b)) (-7) 2) == (-4, 1)   -- divMod
#guard ((fun a b => (Int.tdiv a b, Int.tmod a b)) (-7) 2) == (-3, -1)  -- quotRem
#guard ((fun a => if a < 0 then -1 else if a > 0 then 1 else 0) (-5 : Int)) == -1
#guard ((fun a => if a < 0 then -1 else if a > 0 then 1 else 0) (0 : Int)) == 0
#guard ((Int.gcd (-12) 8 : Int), (Int.lcm 4 6 : Int)) == (4, 12)

-- Task 5: partial functions map to FAITHFUL totals (head/last/!!/fromJust use
-- `default` only on the ⊥ part of the domain), NOT an unconditional `default`.
-- `head xs` emits the faithful `headD default` form, not the literal "default".
def headApp : Expr :=
  .app (.var {name := "GHC.List.head", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "xs", unique := 1, ty := .tyCon "List" [.tyVar "a"], role := .id})
#guard emitExpr [] [] headApp == "((fun xs => xs.headD default)) (xs_1)"
#guard emitExpr [] [] headApp != "default"   -- regression: must NOT blanket-collapse

def fromJustApp : Expr :=
  .app (.var {name := "Data.Maybe.fromJust", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "m", unique := 1, ty := .tyCon "Maybe" [.tyVar "a"], role := .id})
#guard emitExpr [] [] fromJustApp == "((fun m => m.getD default)) (m_1)"

-- Task 5: behavioral locks — the emitted faithful forms compute Haskell
-- semantics on the DEFINED domain, and `default` only where Haskell is ⊥.
#guard ((fun xs => xs.headD default) [1,2,3] : Int) == 1
#guard ((fun xs => xs.headD default) ([] : List Int)) == 0          -- ⊥ → default
#guard (List.tail [1,2,3] : List Int) == [2,3]
#guard (List.tail ([] : List Int)) == []                            -- ⊥ → []
#guard (List.dropLast [1,2,3] : List Int) == [1,2]
#guard ((fun xs => xs.getLastD default) [1,2,3] : Int) == 3
#guard ((fun xs i => xs.getD i.toNat default) [10,20,30] (1 : Int)) == 20
#guard ((fun m => m.getD default) (some 5) : Int) == 5
#guard ((fun m => m.getD default) (none : Option Int)) == 0         -- ⊥ → default

-- Task 6: a case binder referenced in an alt must be bound via `let`.
def caseWithBinder : Expr :=
  let cb : Var := {name := "wild", unique := 7, ty := .tyCon "Int" [], role := .id}
  .case_
    (.var {name := "n", unique := 1, ty := .tyCon "Int" [], role := .id})
    cb (.tyCon "Int" [])
    [ .mk (.litAlt (.litInt 0)) [] (.lit (.litInt 0)),
      .mk .default [] (.var cb) ]   -- DEFAULT references the case binder
#guard ((emitExpr [] [] caseWithBinder).splitOn "let wild_7 :=").length == 2

-- Task 6: an UNUSED case binder must NOT be let-bound (match scrutinee directly).
def caseNoBinder : Expr :=
  let cb : Var := {name := "wild", unique := 8, ty := .tyCon "Int" [], role := .id}
  .case_
    (.var {name := "n", unique := 1, ty := .tyCon "Int" [], role := .id})
    cb (.tyCon "Int" [])
    [ .mk (.litAlt (.litInt 0)) [] (.lit (.litInt 0)),
      .mk .default [] (.lit (.litInt 1)) ]   -- no reference to cb
#guard ((emitExpr [] [] caseNoBinder).splitOn "let wild_8 :=").length == 1

-- Task 7: local recursive let emits `let rec`, not a TODO comment.
def localRecLet : Bind :=
  .rec_ [ ( {name := "go", unique := 3, ty := .tyFun (.tyCon "Int" []) (.tyCon "Int" []), role := .id},
            .lam {name := "k", unique := 4, ty := .tyCon "Int" [], role := .id}
                 (.var {name := "k", unique := 4, ty := .tyCon "Int" [], role := .id}) ) ]
#guard ((emitLet [] [] localRecLet).splitOn "let rec go_3").length == 2
#guard ((emitLet [] [] localRecLet).splitOn "TODO").length == 1   -- no TODO marker

-- Task 8: unboxed Int# arithmetic/comparison primops.
#guard valueMap "GHC.Prim.+#"  == some "(· + ·)"
#guard valueMap "GHC.Prim.-#"  == some "(· - ·)"
#guard valueMap "GHC.Prim.*#"  == some "(· * ·)"
#guard valueMap "GHC.Prim.==#" == some "(· == ·)"
#guard valueMap "GHC.Prim.<#"  == some "(fun a b => decide (a < b))"
#guard valueMap "GHC.Prim.<=#" == some "(fun a b => decide (a ≤ b))"
#guard valueMap "GHC.Prim.>#"  == some "(fun a b => decide (a > b))"
#guard valueMap "GHC.Prim.>=#" == some "(fun a b => decide (a ≥ b))"
#guard valueMap "GHC.Prim./=#" == some "(fun a b => !(a == b))"

-- Task 9: confirm eliminator argument order (behavioral, not string).
-- Confirmed v4.24.0 signatures (via #check):
--   @Option.elim : Option α → β → (α → β) → β        (scrutinee FIRST)
--   @Sum.elim    : (α → γ) → (β → γ) → α ⊕ β → γ      (scrutinee LAST)
#guard (Option.elim (some 5) 0 (fun x => x + 1)) == 6     -- elim o default f : f applied on some
#guard (Option.elim (none : Option Nat) 0 (fun x => x + 1)) == 0
#guard (Option.getD (some 5) 0) == 5
#guard (Option.getD (none : Option Nat) 0) == 0
-- NOTE: confirmed via `#check @Sum.elim` — Sum.elim is scrutinee-LAST:
--   (α → γ) → (β → γ) → α ⊕ β → γ. So Haskell `either f g e` ≡ `Sum.elim f g e`.
#guard (Sum.elim (fun a => a + 10) (fun b => b + 20) (Sum.inl 3 : Sum Nat Nat)) == 13
#guard (Sum.elim (fun a => a + 10) (fun b => b + 20) (Sum.inr 3 : Sum Nat Nat)) == 23

-- Task 9: total Maybe/Either eliminators.
#guard valueMap "GHC.Maybe.maybe"      == some "(fun d f m => Option.elim m d f)"
#guard valueMap "Data.Maybe.fromMaybe" == some "(fun d m => Option.getD m d)"
#guard valueMap "Data.Maybe.isJust"    == some "Option.isSome"
#guard valueMap "Data.Maybe.isNothing" == some "Option.isNone"
#guard valueMap "Data.Either.either"   == some "(fun f g e => Sum.elim f g e)"

-- Tier 3 Task 1: Eq instance emission survives the findEqMethod→findClassMethod refactor.
def eqInstProgram : CoreProgram :=
  [ .nonRec {name := "$c==", unique := 50,
             ty := .tyFun (.tyCon "Foo" []) (.tyFun (.tyCon "Foo" []) (.tyCon "Bool" [])),
             role := .id}
            (.lam {name := "a", unique := 1, ty := .tyCon "Foo" [], role := .id}
                  (.lit (.litInt 0))) ]
def eqInst : Instance :=
  {className := "Eq", headTypes := [.tyCon "Foo" []], dfunName := "$fEqFoo", dfunUnique := 99}
#guard (emitInstance [] [] [] eqInstProgram eqInst).isSome
#guard (((emitInstance [] [] [] eqInstProgram eqInst).getD "").splitOn "instance : BEq (GHCCore.tyConOpaque \"Foo\")").length == 2

-- Tier 3 Task 2/4: Ord is reconstructed via `deriving Ord` + LE/LT/Min/Max in
-- the data block (instances precede binds; Lean instances aren't forward-
-- visible), so `emitInstance` emits nothing for Ord — it's covered by the
-- emitDataDecl guards below.
def ordInst : Instance :=
  {className := "Ord", headTypes := [.tyCon "Foo" []], dfunName := "$fOrdFoo", dfunUnique := 98}
#guard emitInstance [] [] [] [] ordInst == none

-- Tier 3 Task 3: Show instances are intentionally skipped (derived Repr handles printing).
def showInst : Instance :=
  {className := "Show", headTypes := [.tyCon "Foo" []], dfunName := "$fShowFoo", dfunUnique := 97}
#guard emitInstance [] [] [] [] showInst == none

-- Tier 3 Task 4: derived Eq (DecidableEq) and Ord (deriving Ord + LE/LT/Min/Max).
def coinDecl : DataDecl :=
  {name := "Coin", kind := "data",
   ctors := [ {name := "Heads", fields := []}, {name := "Tails", fields := []} ]}
-- derivedEq + hasOrd → inductive carries DecidableEq, Ord + LE/LT/Min/Max.
#guard ((emitDataDecl true true coinDecl).splitOn "deriving Repr, Inhabited, DecidableEq, Ord").length == 2
#guard ((emitDataDecl true true coinDecl).splitOn "instance : LE Coin := leOfOrd").length == 2
#guard ((emitDataDecl true true coinDecl).splitOn "instance : Min Coin := minOfLe").length == 2
-- hasOrd alone (Eq not tag-derived) still gets DecidableEq + Ord + LE/LT.
#guard ((emitDataDecl false true coinDecl).splitOn "DecidableEq, Ord").length == 2
#guard ((emitDataDecl false true coinDecl).splitOn "leOfOrd").length == 2
-- neither → unchanged (no DecidableEq/Ord/LE).
#guard ((emitDataDecl false false coinDecl).splitOn "deriving Repr, Inhabited").length == 2
#guard ((emitDataDecl false false coinDecl).splitOn "DecidableEq").length == 1
#guard ((emitDataDecl false false coinDecl).splitOn "leOfOrd").length == 1
-- derived Eq instance is skipped (deriving handles it); hand-written (empty
-- derived set) still emits its BEq from the translated body.
#guard emitInstance [] [] ["(GHCCore.tyConOpaque \"Foo\")"] eqInstProgram eqInst == none
#guard (emitInstance [] [] [] eqInstProgram eqInst).isSome

-- Dict Task 1: ClassDecl / ClassMethod AST types exist and hold the shape.
-- (Widened to `ClassDecl` v2 by M3 Task 1: `tyVar` → `tyVars`, plus `supers`.
-- `hasDefault` is defaulted, so this single-param no-superclass shape — the only
-- one supported end-to-end — reads exactly as it did in v1.)
def sizedClass : ClassDecl :=
  { name := "Sized", tyVars := ["a"], supers := [],
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
#guard sizedClass.name == "Sized"
#guard sizedClass.methods.head!.hasDefault == false
#guard sizedClass.methods.length == 1
#guard (sizedClass.methods.head!).name == "size"

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
-- M3 Task 2 ADAPTATION: the map is `List MethodRef` (was `List (Name × Name)`),
-- and the reconstruction leaves `shadowedBy` EMPTY — it sees class shapes, not
-- the bodies that get emitted; `emitFullProgram` fills it via
-- `attachMethodShadows`. Pinned so a future caller that forgets that step is a
-- visibly different value, not a silent reversion to name-only matching.
#guard reconRes.2 == [{ method := "size", cls := "Sized" }]
#guard reconRes.2.map (·.shadowedBy) == [([] : List Unique)]
#guard emitType (reconRes.1.head!).methods.head!.ty == emitType (.tyFun (.tyVar "a") (.tyCon "Int" []))
-- M3 Task 1 ADAPTATION guard. `reconstructClasses` was rewritten for `ClassDecl`
-- v2 but is unchanged in substance: it still produces exactly the three
-- structural limits its docstring claims — the single invented `a`, now as a
-- ONE-element `tyVars` list rather than a scalar; `supers` empty (a `$p`
-- superclass selector is not a top-level bind, so nothing here can see one);
-- `hasDefault` false (a `$dm` bind is indistinguishable from an ordinary one).
-- Pinned on the REAL function's output, so the plugin channel's richer shapes
-- can never be confused for something the fallback could have produced.
#guard (reconRes.1.head!).tyVars == ["a"]
#guard (reconRes.1.head!).supers == ([] : List Name)
#guard (reconRes.1.head!).methods.head!.hasDefault == false

-- Dict Task 3: emit a Lean `class` from a ClassDecl.
-- M3 Task 4 ADAPTATION: `emitClassDecl` takes the method-name → default-body
-- list first (`[]` here = no class-body `:=` defaults), so a class without
-- defaults still emits exactly the v1 string.
#guard emitClassDecl [] sizedClass == "class Sized (a : Type) where\n  size : (a → Int)"

-- Dict Task 4: a bare class-method selector emits `Class.method`; others unaffected.
#guard emitVar [{ method := "size", cls := "Sized" }] [] {name := "size", unique := 7, ty := .tyFun (.tyVar "a") (.tyCon "Int" []), role := .id} == "Sized.size"
#guard emitVar [{ method := "size", cls := "Sized" }] [] {name := "other", unique := 8, ty := .tyCon "Int" [], role := .id} == "other_8"

-- Dict Task 5: a user-class instance emits `instance : C T where m := <ref>`.
-- M3 Task 4 ADAPTATION: `emitInstanceUser`/`emitInstance` take the translated
-- (class, method) default set first (`[]` = none), which is what decides whether
-- a missing method is an omitted default or an unresolvable one.
#guard (((emitInstanceUser [] [sizedClass] [csizeBind, dfunBind] sizedInst).getD "").splitOn
         "instance : Sized (GHCCore.tyConOpaque \"Box\") where").length == 2
#guard (((emitInstanceUser [] [sizedClass] [csizeBind, dfunBind] sizedInst).getD "").splitOn
         "size := ").length == 2
-- no matching class → none
#guard emitInstanceUser [] [] [csizeBind, dfunBind] sizedInst == none

-- Dict Task 6: a `C a =>`-constrained def emits `[C a]` and no leaked dict arg.
def totalBind : Bind :=
  .nonRec
    {name := "total", unique := 70,
     ty := .forAll "a" (.tyFun (.tyCon "Sized" [.tyVar "a"])
            (.tyFun (.tyCon "List" [.tyVar "a"]) (.tyCon "Int" []))),
     role := .id}
    (.lam {name := "xs", unique := 71, ty := .tyCon "List" [.tyVar "a"], role := .id}
          (.lit (.litInt 0)))
#guard ((emitBind [] ["Sized"] [] totalBind).splitOn "[Sized a]").length == 2
#guard ((emitBind [] ["Sized"] [] totalBind).splitOn "tyConOpaque \"Sized\"").length == 1

/-! ## M1 Task 2: tuples — 3- and 4-tuple construction, types, patterns -/

-- M1 Task 2: 3-/4-tuple construction. Ctors are eta-expanded lambdas so plain
-- left-application works at any saturation.
-- Names observed from Generated/TupleTriple.lean and its shim JSON
-- (/tmp/transpile-TupleTriple.json, GHC 9.2.7) — same split as the 2-tuple
-- block above:
--   type tycon       : "(,,)" / "(,,,)"                     (bare, in binder types)
--   value-pos ctor   : "GHC.Tuple.(,,)" / "GHC.Tuple.(,,,)" (qualified; resolved to the
--                      eta-expanded lambdas in the generated file, so the arms fired)
--   pattern-pos ctor : "(,,)" / "(,,,)"                     (bare; emitted as
--                      `(a_…, b_…, c_…)` tuple patterns)
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

-- 5+-tuples must stay unmapped (loud compile failure), as the Maps comment promises.
#guard dataConMap "(,,,,)" == none
#guard typeConMap "(,,,,)" ["Int", "Int", "Int", "Int", "Int"] == none

/-! ## M1 Task 3: list literals (`build` / `augment`) -/

-- M1 Task 3: list literals. `[a,b,x3]` desugars to `build (\c n -> c a (c b (c x3 n)))`
-- with `build g = g (:) []`.
-- Type args/binders on `g` are already erased by Lower; emitted lambdas carry
-- no binder type annotations, so the rank-2 type cannot dangle.
-- Names observed from Generated/ListLiterals.lean and its shim JSON
-- (/tmp/transpile-ListLiterals.json, GHC 9.2.7): "GHC.Base.build" (×2, both
-- `smallList = [1,2,3]` and the literal in `withPrefix`). `augment` did NOT
-- appear — `[1,2] ++ xs` desugared to `++ (build ...) xs`, i.e. List.append
-- over an inner build. The augment arm is unreachable at pass-0000 (it comes
-- from the "++" RULE in simplifier passes ≥ 1); kept as a forward hedge in
-- case the dump point ever moves — see the Maps.lean comment.
#guard valueMap "GHC.Base.build"   == some "(fun g => g List.cons List.nil)"
#guard valueMap "GHC.Base.augment" == some "(fun g xs => g List.cons xs)"

-- Semantic pins: the mapped lambdas applied to a real cons-builder must
-- produce the literal list. Catches a wrong-but-intended mapping, which the
-- string guards above cannot; also the only coverage augment can ever get
-- (it is unreachable at pass-0000).
#guard ((fun g => g List.cons List.nil) (fun c n => c (1:Int) (c 2 (c 3 n)))) == [1,2,3]
#guard ((fun g xs => g List.cons xs) (fun c n => c (1:Int) (c 2 n)) [7]) == [1,2,7]

/-! ## M1 Task 4: Int ranges (`enumFromTo` / `enumFromThenTo`) -/

-- M1 Task 4: Int ranges. Semantics pinned against GHC:
--   [1..5]=[1,2,3,4,5]  [3..3]=[3]  [3..1]=[]
--   [1,3..9]=[1,3,5,7,9]  [1,3..8]=[1,3,5,7]  [10,8..5]=[10,8,6]
--   [5,7..4]=[]  [5,3..6]=[]  [1,1..0]=[]  ([1,1..5] is infinite ⇒ default=[])
-- Names observed in this pipeline from Generated/ListLiterals.lean and its shim
-- JSON (/tmp/transpile-ListLiterals.json, GHC 9.2.7), same as the Task 2/3
-- blocks above:
--   "GHC.Enum.enumFromTo"      (×1, from `rangeList = [1 .. 5]`)
--   "GHC.Enum.enumFromThenTo"  (×1, from `countdown = [10, 8 .. 5]`)
--   "GHC.Enum.$fEnumInt"       (×2, the Enum dict — erased by Lower)
-- The specialised `GHC.Enum` workers `eftInt`/`efdtInt` do NOT appear at
-- pass-0000 (they come from RULES in simplifier passes ≥ 1), so the class-method
-- names above are the live path. Both mapped names fired: the generated file
-- contains `Hs.enumFromTo` / `Hs.enumFromThenTo` with no unmapped residue.
#guard valueMap "GHC.Enum.enumFromTo"     == some "Hs.enumFromTo"
#guard valueMap "GHC.Enum.enumFromThenTo" == some "Hs.enumFromThenTo"

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
-- Soundness pin for the documented ⊥ → `default` convention: `[1,1..5]` is an
-- INFINITE list in GHC, so every total observation of it is ⊥ and it lowers to
-- `default` (= `[]`). The `1 1 0` guard above cannot distinguish this branch
-- from the finite-empty one — they share the `d = 0` arm — so this line is the
-- only tested record that the `default` arm is deliberate, not an oversight.
#guard Hs.enumFromThenTo 1 1 5 == []

/-! ## M1 Task 5: Int-indexed ops (`take` / `drop` / `splitAt` / `replicate`) -/

-- M1 Task 5: Int-indexed ops. Haskell take/drop/replicate/splitAt treat a
-- negative count as 0 (`take n _ | n <= 0 = []`, `drop n xs | n <= 0 = xs`,
-- `replicate = take n (repeat x)`, `splitAt n xs = (take n xs, drop n xs)`);
-- `Int.toNat` clamps negatives to 0 and `List.take 0 = []` / `List.drop 0 = id`
-- / `List.replicate 0 = []` — so the semantics MATCH on the whole domain.
-- Names observed from /tmp/transpile-ListLibrary.json (GHC 9.2.7, pass-0000)
-- and Generated/ListLibrary.lean:
--   "GHC.List.take"  "GHC.List.drop"  "GHC.List.splitAt"  "GHC.List.replicate"
-- (×1 each). Unlike `length`/`null`/`foldr` above, these are NOT Foldable
-- methods post-FTP, so no `Data.Foldable.*` alternative is needed — all four
-- keys fired and the generated file has no `GHC.List.*` residue. GHC eta-reduces
-- `takeSome n xs = take n xs` to `takeSome = take`, so the mapped strings appear
-- point-free; `Hs.splitAt`'s implicit `α` resolves from the emitted signature.
-- The APPLIED form `((fun n xs => …) (a)) (b)` (which a non-eta-reducible use in
-- a later task will produce) also elaborates: the unannotated binder types are
-- postponed and resolved from the argument types.
#guard valueMap "GHC.List.take"      == some "(fun n xs => List.take n.toNat xs)"
#guard valueMap "GHC.List.drop"      == some "(fun n xs => List.drop n.toNat xs)"
#guard valueMap "GHC.List.splitAt"   == some "Hs.splitAt"
#guard valueMap "GHC.List.replicate" == some "(fun n x => List.replicate n.toNat x)"
-- `List Int` ascriptions: unannotated numeric list literals default to `Nat`,
-- but `Int` is the element type the transpiler actually emits.
#guard Hs.splitAt 1 ([5, 6, 7] : List Int) == ([5], [6, 7])
#guard Hs.splitAt (-2) ([1] : List Int) == ([], [1])
#guard Hs.splitAt 9 ([1] : List Int) == ([1], [])
-- The unannotated APPLIED form really does elaborate (binder types postponed,
-- then resolved from the argument types) — this is the load-bearing check for
-- the claim in the block comment above, not just prose.
#guard ((fun n xs => List.take n.toNat xs) (2 : Int) ([1,2,3] : List Int)) == [1,2]
-- Semantic pins for the inline lambdas (negative-clamp + arg order):
#guard ((fun (n : Int) (xs : List Int) => List.take n.toNat xs) 2 [1,2,3]) == [1,2]
#guard ((fun (n : Int) (xs : List Int) => List.take n.toNat xs) (-1) [1,2,3]) == []
#guard ((fun (n : Int) (xs : List Int) => List.drop n.toNat xs) 1 [1,2,3]) == [2,3]
-- `drop` is the one op whose clamp differs in KIND: take/replicate/splitAt-fst
-- clamp to "empty", drop clamps to "unchanged". Pin it directly.
#guard ((fun (n : Int) (xs : List Int) => List.drop n.toNat xs) (-1) [1,2,3]) == [1,2,3]
#guard ((fun (n : Int) (x : Int) => List.replicate n.toNat x) 3 9) == [9,9,9]
#guard ((fun (n : Int) (x : Int) => List.replicate n.toNat x) (-3) 9) == []

/-! ## M1 Task 6 — zip family (zip, zipWith, unzip) -/

-- Names observed from /tmp/transpile-ListLibrary.json (GHC 9.2.7, pass-0000)
-- and Generated/ListLibrary.lean:
--   "GHC.List.zip"  "GHC.List.zipWith"  "GHC.List.unzip"   (×1 each)
-- A bare grep for `zip` over the dump found NOTHING else — in particular no
-- `Data.OldList.unzip` and no `GHC.Base.zip`, so no alternative keys are needed
-- (`Data.OldList` only re-exports these; the desugarer names the GHC.List
-- originals). Unlike `length`/`null`/`foldr`, none of the three is a Foldable
-- method post-FTP, so there is no `Data.Foldable.*` form either.
-- Semantics: Haskell's `zip`/`zipWith` truncate to the SHORTER list
-- (`zipWith f (a:as) (b:bs) = f a b : zipWith f as bs; zipWith _ _ _ = []`) and
-- so do Lean's. Lean's `List.zip` is `zipWith Prod.mk`, structurally recursive
-- on both lists — NOT an accumulator, so unlike `List.splitAt` (which is why
-- `Hs.splitAt` exists above) it reduces the same way Haskell's does in proofs
-- and needs no `Hs.*` wrapper. Haskell's `unzip` is a `foldr` with a lazy
-- pattern `~(as,bs)` and seed `([],[])`; it agrees with `List.unzip` on every
-- FINITE list, which is the transpiler's domain.
-- Emission shapes — both elaborate. All the fixture defs are written WITH
-- binders (`pairUp xs ys = zip xs ys`, `addWise xs ys = zipWith (+) xs ys`,
-- `split2 ps = unzip ps`); what differs is whether GHC eta-reduces them. It
-- does for `pairUp` and `split2`, so their CORE defs are point-free and the
-- mapping string lands as the entire body: a bare lambda `(fun xs ys =>
-- List.zip xs ys)` for `pairUp`, and the bare name `List.unzip` for `split2`
-- (point-free in Core ≠ point-free in the emitted term — only `split2`'s is).
-- `addWise`/`subWise` are NOT eta-reduced at pass-0000, so their binders
-- survive into Lean and the mapping string is emitted in APPLIED position:
-- `(((fun f xs ys => …) (· + ·)) xs) ys`.
-- Eta-wrapped for arity legibility only (definitionally equal to the bare
-- names — the wrap itself pins nothing; the (· - ·) semantic pins below do).
#guard valueMap "GHC.List.zip"     == some "(fun xs ys => List.zip xs ys)"
#guard valueMap "GHC.List.zipWith" == some "(fun f xs ys => List.zipWith f xs ys)"
#guard valueMap "GHC.List.unzip"   == some "List.unzip"
#guard valueMap "Data.List.unzip"  == some "List.unzip"   -- plan hedge (unobserved at pass-0000)
-- The hedge asymmetry is deliberate, not an oversight: `unzip` is the only one
-- of the three with a `Data.List` alternative key because the M1 plan mandated
-- exactly that key. `zip`/`zipWith` were observed `GHC.List.*`-only (see the
-- grep note above) and the plan states no hedge for them, so they get none.
-- Semantic pins: catch a Lean-side signature/arg-order surprise at build time.
-- `List Int` ascriptions for the same reason as the Task 5 block: unannotated
-- numeric list literals default to `Nat`, but `Int` is what the transpiler emits.
-- Arg order must be pinned with a NON-commutative op — `(· + ·)` would pass even
-- if `List.zipWith`'s two list args were swapped.
-- FOUR guards in this block share the RHS `[9, 18]`; they are NOT duplicates and
-- none subsumes another, so a future cleanup must not delete any of them:
--   (1) the equal-length one just below pins ARG ORDER (a flip yields [-9,-18]);
--   (2) `[10,20,30] - [1,2]` pins LEFT-longer truncation;
--   (3) `[10,20] - [1,2,3]` pins RIGHT-longer truncation (a `zipWith` that
--       truncated only one way would still satisfy (1) and (2));
--   (4) the applied-shape guard `(((fun f xs ys => …) (· - ·)) …)` at the end
--       of this block pins that the APPLIED emission shape ELABORATES — a
--       property of the emitted term, not of `List.zipWith`.
#guard List.zipWith (· - ·) ([10, 20] : List Int) [1, 2] == [9, 18]
-- Truncation to the shorter list, pinned in BOTH directions (Haskell's
-- `zip (x:xs) (y:ys) = …; zip _ _ = []` truncates either way; so does Lean's) —
-- for `zip` and for `zipWith` alike.
#guard List.zip ([1, 2] : List Int) [10, 20, 30] == [(1, 10), (2, 20)]
#guard List.zip ([1, 2, 3] : List Int) [10, 20] == [(1, 10), (2, 20)]
#guard List.zipWith (· - ·) ([10, 20, 30] : List Int) [1, 2] == [9, 18]
#guard List.zipWith (· - ·) ([10, 20] : List Int) [1, 2, 3] == [9, 18]   -- right-longer truncation
#guard List.unzip ([(1, 10), (2, 20)] : List (Int × Int)) == ([1, 2], [10, 20])
-- Base case: Haskell `unzip [] = ([], [])` (its `foldr` seed is `([], [])`).
#guard List.unzip ([] : List (Int × Int)) == ([], [])
-- Empty-list cases on both sides — the ground instances of the `pairUp_nil`
-- theorem in examples/haskell/ListLibrary.hs. Note `zipWith f l [] = []` is NOT
-- definitional in Lean (core proves it `by simp [zipWith]`, not `rfl`, because
-- it needs a case split on `l`); Blaster discharges the quantified form anyway.
#guard List.zip ([1, 2, 3] : List Int) ([] : List Int) == []
#guard List.zip ([] : List Int) ([1, 2, 3] : List Int) == []
-- The APPLIED form GHC emits for `addWise xs ys = zipWith (+) xs ys` — the
-- unannotated mapping lambda applied to `(+)` and then to the def's own two
-- binders, since this def does NOT eta-reduce to a point-free Core def the way
-- `pairUp`/`split2` do — really does elaborate: the binder types are postponed
-- and resolved from the argument types. Load-bearing for the emission-shapes
-- claim in the block comment above.
#guard ((((fun f xs ys => List.zipWith f xs ys)) ((· - ·))) ([10, 20] : List Int)) [1, 2] == [9, 18]

/-! ## M1 Task 7 — folds and predicates (sum, product, all, any, and, or) -/

-- Names observed from /tmp/transpile-ListLibrary.json (GHC 9.2.7, pass-0000).
-- ALL SIX resolve through `Data.Foldable.*`; a grep for `GHC.List.sum` /
-- `.product` / `.all` / `.any` / `.and` / `.or` found ZERO occurrences, so the
-- `GHC.List.*` keys below are unobserved hedges (kept, per the never-remove-a-
-- hedge rule, matching the length/null/foldr arms). Core, dicts and all:
--   sumList  = \xs -> Data.Foldable.sum @[] $fFoldable[] @Int $fNumInt xs
--   conj     = \bs -> Data.Foldable.and @[] $fFoldable[] bs
--   allPos   = \xs -> Data.Foldable.all @[] @Int $fFoldable[] (\v -> v > 0) xs
-- Two DICT shapes appear here that no previously-mapped Foldable name had:
-- `sum`/`product` carry TWO dicts ($fFoldable[] *and* $fNumInt, `length`
-- carries one), and `all`/`any`/`and`/`or` are not class methods at all but
-- constrained plain functions. Lower erases every one of them: the emitted
-- Lean is `(fun xs => List.foldl (· + ·) 0 xs) (xs_2395)` and `Hs.and (bs)` —
-- no stray dict argument, so both new shapes land at the mapped arity.
-- `sum`/`product` use explicit foldl matching GHC (`sum = foldl (+) 0`) rather
-- than core's `List.sum`, for two concrete reasons: (a) v4.24 core has NO
-- `List.product` at all, so `product` has to be hand-rolled either way and
-- symmetry argues for hand-rolling `sum` with it; (b) core's `List.sum` is
-- `foldr (· + ·) 0` (Init/Data/List/Basic.lean:2066) whereas GHC's `sum` is
-- `foldl (+) 0`, so the explicit foldl is the more faithful image. At Int, foldl
-- vs foldr order is unobservable anyway (+/* are associative and commutative
-- and both sides are total). Base cases match GHC: sum [] = 0, product [] = 1,
-- and [] = True, or [] = False, all p [] = True, any p [] = False.
-- The all/any wraps are LOAD-BEARING (Lean's List.all takes the list first;
-- Haskell takes the predicate first) — unlike the zip-family legibility wraps.
-- List COMPREHENSIONS also land in this block. `[2 * x | x <- xs]` desugars at
-- pass-0000 to
--   GHC.Base.build @Int (\a c n -> GHC.Base.foldr @Int @b
--                                    (\ds ds' -> c (2 * ds) ds') n xs)
-- i.e. through `GHC.Base.foldr`, NOT `Data.Foldable.foldr` — the first
-- transpile loud-failed with `GHC.Base.foldr` residue in the emitted file.
-- It is the list-specialised `foldr :: (a->b->b) -> b -> [a] -> b`: two type
-- args, then `(f) (z) (xs)`, and NO dict (checked in the JSON), so it is the
-- same shape as the dict-erased Foldable form and was added as a third
-- alternative on the EXISTING foldr arm rather than as a new mapping.
#guard valueMap "Data.Foldable.sum"     == some "(fun xs => List.foldl (· + ·) 0 xs)"
#guard valueMap "GHC.List.sum"          == some "(fun xs => List.foldl (· + ·) 0 xs)"
#guard valueMap "Data.Foldable.product" == some "(fun xs => List.foldl (· * ·) 1 xs)"
#guard valueMap "GHC.List.product"      == some "(fun xs => List.foldl (· * ·) 1 xs)"
#guard valueMap "Data.Foldable.all"     == some "(fun p xs => List.all xs p)"
#guard valueMap "GHC.List.all"          == some "(fun p xs => List.all xs p)"
#guard valueMap "Data.Foldable.any"     == some "(fun p xs => List.any xs p)"
#guard valueMap "GHC.List.any"          == some "(fun p xs => List.any xs p)"
#guard valueMap "Data.Foldable.and"     == some "Hs.and"
#guard valueMap "GHC.List.and"          == some "Hs.and"
#guard valueMap "Data.Foldable.or"      == some "Hs.or"
#guard valueMap "GHC.List.or"           == some "Hs.or"
-- The comprehension key, sharing the pre-existing `Data.Foldable.foldr` arm
-- (whose `GHC.List.foldr` guard lives at the top of this file).
-- OBSERVED (unlike the GHC.List.* hedges above): this is the one alternative
-- in this block that a live fixture (`doubled`) actually exercises.
#guard valueMap "GHC.Base.foldr"        == some "(fun f z xs => List.foldr f z xs)"
-- Semantic pins.
#guard Hs.and [true, true] == true
#guard Hs.and [true, false] == false
#guard Hs.and [] == true
#guard Hs.or [false, true] == true
#guard Hs.or [] == false
-- Load-bearing, not a duplicate: the all-false case is the ONLY guard that
-- distinguishes `Hs.or`'s body `xs.any id` from `xs.any (fun _ => true)`,
-- which satisfies every other `or` guard here. (`Hs.and`'s analogous case is
-- already covered by the `[true, false]` guard above.)
#guard Hs.or [false, false] == false
#guard ((fun xs => List.foldl (· + ·) 0 xs) ([1,2,3] : List Int)) == 6
#guard ((fun xs => List.foldl (· * ·) 1 xs) ([2,3,4] : List Int)) == 24
#guard ((fun xs => List.foldl (· + ·) 0 xs) ([] : List Int)) == 0
-- all/any arg-order pins with a NON-symmetric predicate (a flipped wrap would
-- feed the list where the predicate goes — loud type error — but pin anyway):
#guard ((fun p xs => List.all xs p) (fun x => decide (x > (0:Int))) [1,2]) == true
#guard ((fun p xs => List.all xs p) (fun x => decide (x > (0:Int))) [1,0]) == false
#guard ((fun p xs => List.any xs p) (fun x => decide (x == (0:Int))) [1,0]) == true
#guard ((fun p xs => List.any xs p) (fun x => decide (x == (0:Int))) [1,2]) == false
-- Comprehension shape: the foldr mapping applied the way the desugared
-- `[2 * x | x <- xs]` applies it — cons-ing consumer, nil seed, list last.
-- Pins the (f, z, xs) arg order on the arm `GHC.Base.foldr` now shares.
#guard ((fun f z xs => List.foldr f z xs)
          (fun a b => List.cons (2 * a) b) ([] : List Int) ([1,2,3] : List Int)) == [2,4,6]

/-! ## M1 Task 8 — search and flatten (elem, notElem, lookup, concat, concatMap) -/

-- Names observed from /tmp/transpile-ListLibrary.json (GHC 9.2.7, pass-0000):
--   Data.Foldable.elem / .notElem / .concat / .concatMap   (post-FTP Foldable)
--   GHC.List.lookup                                        (not a Foldable method)
-- NEGATIVES, all checked by extracting every qualified `GHC.*`/`Data.*` name in
-- the JSON: ZERO occurrences of `GHC.List.elem`, `GHC.List.notElem`,
-- `GHC.List.concat`, `GHC.List.concatMap` or `Data.List.lookup`. Those five keys
-- are therefore UNOBSERVED hedges, kept per the never-remove-a-hedge rule
-- (matching the length/null/sum/all family above). Core spines verbatim (`@ty`
-- = an erased type application), dicts and all:
--   hasZero    = \xs -> elem @ty Data.Foldable.$fFoldable[] @ty
--                            GHC.Classes.$fEqInt (I# 0) xs
--   misses     = \x xs -> notElem @ty @ty Data.Foldable.$fFoldable[]
--                                 GHC.Classes.$fEqInt x xs
--   lookupOr   = \k ps -> Data.Maybe.fromMaybe @ty (I# 0)
--                           (GHC.List.lookup @ty @ty GHC.Classes.$fEqInt k ps)
--   flattenAll = \xss -> concat @ty @ty Data.Foldable.$fFoldable[] xss
--   dupEach    = \xs -> concatMap @ty @ty @ty Data.Foldable.$fFoldable[]
--                         (\x -> build @ty (\a c n -> c x (c x n))) xs
-- Note the DICT INTERLEAVING is not uniform: `elem` puts the Foldable dict
-- BETWEEN its two type args, while `notElem` (same arity, same two classes)
-- puts both type args first. Nothing in this pipeline may assume a fixed
-- dict/type-arg order — Lower erases each `@ty`/dict wherever it sits, which is
-- why both land at the mapped arity regardless. `concatMap` carries THREE type
-- args and `concat` two, also erased.
-- elem/notElem/lookup use BEq (the project's Eq image — hand-written Haskell
-- `Eq` instances become `BEq` instances, and `$fEqInt` is erased by Lower along
-- with `$fFoldable[]`, so the mapping lands at the mapped arity).
-- Why these wraps exist, and which heads need none: see the arm comment in
-- Maps.lean — LOAD-BEARING adapters (`List.contains`, an `abbrev` in
-- `Init/Data/List/Basic.lean`, is reached receiver-first, so Haskell's
-- element-FIRST arg order has to be adapted).
-- SCOPE NOTE (unverified, out of scope): every fixture def here is at `Int`, so
-- whether a POLYMORPHIC Haskell def with an `Eq a` constraint transpiles is
-- untested — it would need `emitDefHeader` to synthesize a `[BEq t]` binder the
-- way it already does `[Inhabited t]` for the partial-default names.
#guard valueMap "Data.Foldable.elem"    == some "(fun x xs => xs.contains x)"
#guard valueMap "GHC.List.elem"         == some "(fun x xs => xs.contains x)"
#guard valueMap "Data.Foldable.notElem" == some "(fun x xs => !(xs.contains x))"
#guard valueMap "GHC.List.notElem"      == some "(fun x xs => !(xs.contains x))"
#guard valueMap "GHC.List.lookup"       == some "(fun k ps => ps.lookup k)"
#guard valueMap "Data.List.lookup"      == some "(fun k ps => ps.lookup k)"
#guard valueMap "Data.Foldable.concat"  == some "List.flatten"
#guard valueMap "GHC.List.concat"       == some "List.flatten"
#guard valueMap "Data.Foldable.concatMap" == some "(fun f xs => xs.flatMap f)"
#guard valueMap "GHC.List.concatMap"      == some "(fun f xs => xs.flatMap f)"
-- Semantic pins. `List Int` ascriptions for the same reason as the Task 5/6
-- blocks: unannotated numeric list literals elaborate at `Nat`, but `Int` is
-- what the transpiler emits.
#guard (([1, 2, 3] : List Int).contains 2) == true
#guard (([1, 2, 3] : List Int).contains 9) == false
#guard (([(1, 10), (2, 20)] : List (Int × Int)).lookup 2) == some 20
#guard (([(1, 10)] : List (Int × Int)).lookup 9) == none
#guard (([(1, 10), (1, 20)] : List (Int × Int)).lookup 1) == some 10   -- FIRST match, like Haskell
#guard (([[1], [2, 3]] : List (List Int)).flatten) == [1, 2, 3]
#guard (([] : List (List Int)).flatten) == []
#guard (([1, 2] : List Int).flatMap (fun x => [x, x])) == [1, 1, 2, 2]
-- APPLIED-shape guards, the load-bearing analogue of the applied-shape
-- `zipWith` guard in the M1 Task 6 block. The pins above use dot notation on a
-- literal, where the receiver type is already known; the EMITTED code applies
-- the mapping lambda with UNANNOTATED binders
-- (`((fun x xs => xs.contains x) 0 xs_123)`), where the binder type is still a
-- metavariable when the field notation is elaborated. These guards are the only
-- ones that pin that that postponement resolves — the dot-notation pins above
-- pass either way.
#guard ((fun x xs => xs.contains x) (2 : Int) [1, 2, 3]) == true
#guard ((fun x xs => !(xs.contains x)) (9 : Int) [1, 2, 3]) == true
#guard ((fun k ps => ps.lookup k) (2 : Int) [(1, 10), (2, 20)]) == some 20
#guard ((fun f xs => xs.flatMap f) (fun x => [x, x]) ([1, 2] : List Int)) == [1, 1, 2, 2]

-- MULTI-GENERATOR comprehension probe (`pairsUpTo n = [(x, y) | x <- [1 .. n],
-- y <- [1 .. x]]`). A prior reviewer warned the Task-7 single-generator
-- observation might not generalize. It does, and it needed ZERO new mappings:
-- pass-0000 desugars the nested generators to ONE `GHC.Base.build` wrapping TWO
-- nested `GHC.Base.foldr`s, the inner fold's seed being the outer fold's
-- accumulator, with the ranges as `GHC.Enum.enumFromTo` and the tuple as
-- `GHC.Tuple.(,)` (transcribed from the emitted Lean, with the erased type
-- binder on `build`'s argument dropped):
--   pairsUpTo = \n -> build (\c n' ->
--     foldr (\ds ds' -> foldr (\dt dt' -> c (ds, dt) dt') ds' (enumFromTo 1 ds))
--           n' (enumFromTo 1 n))
-- Every head there was already mapped (build / GHC.Base.foldr / enumFromTo /
-- Prod.mk), so no arm was added for it.
-- This also STRENGTHENS the "observed: 0 occurrences at pass-0000" claim on the
-- `GHC.Base.augment` arm (Maps.lean): a nested comprehension was the most
-- plausible way that claim could have gone stale, and `augment` still does not
-- appear (grep of the JSON: 0).

-- Nested tycon applications in TYPE position. `flattenAll :: [[Int]] -> [Int]`
-- is the first M1 fixture to nest one tycon inside another, and it exposed a
-- PRE-EXISTING defect: the juxtaposition arms spliced their args unparenthesized,
-- so `[[Int]]` emitted the ill-typed `List List Int` (loud fail — an
-- "Application type mismatch", never silent-wrong). `Maybe [Int]` → `Option List
-- Int` and `[Maybe Int]` → `List Option Int` were broken the same way. Fixed by
-- routing those arms through `Maps.parenArg`. Both branches of that helper are
-- pinned below, because the zero-churn property (atomic and already-bracketed
-- args are left ALONE) matters as much as the fix: it is what keeps every
-- previously-emitted annotation byte-identical.
#guard typeConMap "List"   ["Int"]              == some "List Int"          -- atomic: unchanged
#guard typeConMap "[]"     ["List Int"]         == some "List (List Int)"   -- the fix
#guard typeConMap "Maybe"  ["List Int"]         == some "Option (List Int)"
#guard typeConMap "List"   ["(Int × Int)"]      == some "List (Int × Int)"  -- bracketed: unchanged
#guard typeConMap "Either" ["List Int", "Int"]  == some "Sum (List Int) Int"
#guard typeConMap "Either" ["Int", "List Int"]  == some "Sum Int (List Int)"  -- 2nd call site
-- Tuple arms need no `parenArg`: `×` is `infixr:35`, BELOW application, so a
-- juxtaposed arg already binds tighter than the `×` around it.
#guard typeConMap "(,)"    ["List Int", "Int"]  == some "(List Int × Int)"

/-! ## M1 Task 9 — partial maximum and minimum (bottom path) -/

-- maximum/minimum are ⊥ ONLY on []. Like head/last they map to a getD-default
-- form: faithful on nonempty, `default` exactly where Haskell is ⊥. Semantics
-- caveat: Haskell maximum needs Ord; Lean's List.max? folds Max.max. They agree
-- at Int (M1's whole surface). On a user type with hand-written non-structural
-- Ord, Max comes from the structural deriving route — the pre-existing README
-- limitation; this task does not widen it. That divergence is BOUNDED by a
-- loud failure rather than silent wrongness on the types most likely to expose
-- it: core Lean has no `Max` for products (`#synth Max (Int × Int)` = "failed to
-- synthesize"), so `maximum` on a tuple element type does not elaborate at all
-- instead of quietly disagreeing with Haskell's lexicographic `Ord`.
-- Names observed from /tmp/transpile-ListLibrary.json (GHC 9.2.7, pass-0000):
--   Data.Foldable.maximum / .minimum                        (post-FTP Foldable)
-- NEGATIVES: ZERO occurrences of `GHC.List.maximum`, `GHC.List.minimum`, or any
-- `GHC.OldList.*` / `$c`-prefixed method selector. Those two GHC.List keys are
-- therefore UNOBSERVED hedges, kept per the never-remove-a-hedge rule (matching
-- the elem/notElem/concat family above). Core spines verbatim (`@ty` = an erased
-- type application):
--   maxOf = \xs -> maximum @ty Data.Foldable.$fFoldable[] @ty
--                          GHC.Classes.$fOrdInt xs
--   minOf = \xs -> minimum @ty Data.Foldable.$fFoldable[] @ty
--                          GHC.Classes.$fOrdInt xs
-- The `Ord` dict here is NOT new ground: it erases exactly like the `$fOrdInt`
-- already carried by the pre-existing comparison arms — `allPos` in this same
-- fixture desugars its `> 0` through `GHC.Classes.$fOrdInt` (a grep of
-- /tmp/transpile-ListLibrary.json finds `$fOrdInt` in exactly three binds:
-- maxOf, minOf, allPos), and comparison arms have carried it since the Tier era.
-- Erasure is not an Eq/Foldable/Num/Ord-shaped whitelist at all: Lower erases on
-- the binder's `.dict` ROLE, which the shim assigns from GHC's `DFunId` details
-- or a `$d`/`$f` name prefix (shim/Main.hs `binderRole`) — so `$fOrdInt` erases
-- like any other, and the mapping lands at arity 1. Confirmed
-- in the emitted code: `def maxOf (xs_… : List Int) : Int :=
-- ((fun xs => (List.max? xs).getD default)) (xs_…)` — one argument, no dict.
#guard valueMap "Data.Foldable.maximum" == some "(fun xs => (List.max? xs).getD default)"
#guard valueMap "GHC.List.maximum"      == some "(fun xs => (List.max? xs).getD default)"
#guard valueMap "Data.Foldable.minimum" == some "(fun xs => (List.min? xs).getD default)"
#guard valueMap "GHC.List.minimum"      == some "(fun xs => (List.min? xs).getD default)"
-- Semantic pins: faithful on nonempty, default (= 0 for Int) exactly on [].
#guard ((List.max? ([3, 1, 2] : List Int)).getD default) == 3
#guard ((List.min? ([3, 1, 2] : List Int)).getD default) == 1
#guard ((List.max? ([-5, -2] : List Int)).getD default) == -2
#guard ((List.max? ([] : List Int)).getD default) == 0    -- ⊥ → default
#guard ((List.min? ([] : List Int)).getD default) == 0    -- ⊥ → default
-- APPLIED-shape guards, LOAD-BEARING here (not optional as in the Task 8 block).
-- The pins above ascribe `List Int` at the call site, so `Max Int` is resolved
-- against a known type. The EMITTED code applies the mapping lambda with an
-- UNANNOTATED binder (`((fun xs => (List.max? xs).getD default)) (xs_1)`), where
-- `α` is still a metavariable when `List.max?`'s `[Max α]` and `getD`'s
-- `[Inhabited α]` are looked up. `Max Int`/`Min Int` resolve to Int's own core
-- instances — `#synth Max Int` = `Int.instMax`, `#synth Min Int` = `Int.instMin`
-- in v4.24.0, NOT an `Ord`-derived route — so nothing here depends on
-- `LinearOrder`-style instance search; these guards are what pin that the
-- postponement resolves at all.
#guard ((fun xs => (List.max? xs).getD default) ([3, 1, 2] : List Int)) == 3
#guard ((fun xs => (List.min? xs).getD default) ([3, 1, 2] : List Int)) == 1
#guard ((fun xs => (List.max? xs).getD default) ([] : List Int)) == 0
-- Also note `List.maximum?`/`List.minimum?` do NOT exist in v4.24.0 (checked:
-- "Unknown constant"); `List.max?`/`List.min?` are the current names.
-- emitExpr-level pin, mirroring the `headApp`/`fromJustApp` guards in the
-- pre-M1 "Task 5: partial functions" block above: `maximum xs` must emit the
-- faithful getD form, never a blanket `default`.
def maximumApp : Expr :=
  .app (.var {name := "Data.Foldable.maximum", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "xs", unique := 1, ty := .tyCon "List" [.tyVar "a"], role := .id})
#guard emitExpr [] [] maximumApp == "((fun xs => (List.max? xs).getD default)) (xs_1)"
#guard emitExpr [] [] maximumApp != "default"   -- regression: must NOT blanket-collapse
-- `exprHasBottom` must see through maximum/minimum (they mention `default`), so
-- a POLYMORPHIC def using one gets an `[Inhabited t]` binder from
-- `emitDefHeader`. Both members of each hedge pair are registered in
-- `Emit.isPartialDefaultName`: a one-sided registration would silently skip the
-- binder for whichever key Core actually delivers.
-- The [Inhabited t] binder path: a POLYMORPHIC def whose body applies a
-- registered partial name must get the binder. One guard per registered name
-- (this is what enforces the "both members of each hedged pair" claim above).
def mkPartialBind (nm : String) : Bind :=
  .nonRec
    {name := "poly", unique := 90,
     ty := .forAll "a" (.tyFun (.tyCon "List" [.tyVar "a"]) (.tyVar "a")), role := .id}
    (.lam {name := "xs", unique := 91, ty := .tyCon "List" [.tyVar "a"], role := .id}
      (.app (.var {name := nm, unique := 92, ty := .tyVar "a", role := .id})
            (.var {name := "xs", unique := 91, ty := .tyCon "List" [.tyVar "a"], role := .id})))
-- Emitted for the maximum arm (checked): `def poly {a : Type} [Inhabited a]
-- (xs_91 : List a) : a := ((fun xs => (List.max? xs).getD default)) (xs_91)`.
-- `splitOn … == 2` asserts EXACTLY ONE `[Inhabited a]`, so a shape change in
-- either direction (binder dropped, or duplicated per-tyvar) trips the guard.
#guard ((emitBind [] [] [] (mkPartialBind "Data.Foldable.maximum")).splitOn "[Inhabited a]").length == 2
#guard ((emitBind [] [] [] (mkPartialBind "GHC.List.maximum")).splitOn "[Inhabited a]").length == 2
#guard ((emitBind [] [] [] (mkPartialBind "Data.Foldable.minimum")).splitOn "[Inhabited a]").length == 2
#guard ((emitBind [] [] [] (mkPartialBind "GHC.List.minimum")).splitOn "[Inhabited a]").length == 2
-- NON-VACUITY: the same shape with an UNREGISTERED name must get NO binder.
-- Without this, the four positives above would still pass if `emitDefHeader`
-- emitted `[Inhabited a]` unconditionally for every polymorphic def — i.e. they
-- would pin nothing about `isPartialDefaultName`. This is what makes them
-- load-bearing.
#guard ((emitBind [] [] [] (mkPartialBind "GHC.List.reverse")).splitOn "[Inhabited a]").length == 1
-- REACHABILITY NOTE: the four guards above ARE the pin for that binder path —
-- it is covered at unit level, and only there. It stays UNREACHABLE end-to-end,
-- and landing the missing `Ord a` constraint support would NOT be enough to open
-- it. Every fixture def is monomorphic at `Int` (where `Inhabited Int` is found
-- by ordinary instance resolution and no binder is emitted — verified in the
-- generated ListLibrary.lean). A polymorphic `maximum` wrapper would need an
-- `Ord a` constraint in its signature, which this transpiler does not yet
-- support for builtin classes (known deferral) — that support is NECESSARY but
-- NOT SUFFICIENT: core Lean's `Ord α` does not yield `Max α` (checked: `example
-- {α : Type} [Ord α] : Max α := inferInstance` → "failed to synthesize Max α"),
-- and `emitDefHeader` emits `{a : Type}`, `[Inhabited a]` and user-class
-- constraints only — never a `[Max a]` binder. So the polymorphic route would
-- still fail loud on `failed to synthesize Max a` at the `List.max?` call.
-- Fail-loud either way, never silent-wrong; a `[Max a]`/`[Min a]` binder is the
-- work that would actually open the path. Same shape as the Task 8 SCOPE NOTE
-- about `[BEq t]`.
-- BLASTER DATA POINT: both quantified fixture goals went through `List.max?`/
-- `List.min?`/`Option.getD` on the FIRST try, no `decide` fallback needed
-- (`maxOf_singleton : ∀ a, maxOf [a] = a`, and `minOf_pair : ∀ a b,
-- minOf [a, b] = if a < b then a else b`, which additionally makes blaster
-- bridge Lean's `≤`-shaped Int min against a STRICT `<` in the statement — they
-- agree only because both branches give the same value at `a = b`). Blaster
-- also FALSIFIES the near-miss variants with real counterexamples (checked:
-- `maxOf [a] = a + 1` → a := 0; `minOf [a, b] = if a < b then b else a` →
-- a := -1, b := 0; `maxOf [a, b] = a` → a := -1, b := 0), so the ✅s are not
-- vacuous — its Option/max? encoding is genuinely modelling the fold.

/-! ## M1 loud-fail boundary — infinite list producers stay unmapped -/

-- The README promises these are loud compile errors by design. Pin it, so a
-- future well-meaning "let's map iterate" breaks this guard and has to face
-- the infinity question deliberately. (`enumFromThenTo`'s zero-stride corner
-- is the one deliberate exception — ⊥ → `default`, see Runtime.lean.)
#guard valueMap "GHC.List.iterate"    == none
#guard valueMap "GHC.List.repeat"     == none
#guard valueMap "GHC.List.cycle"      == none
#guard valueMap "GHC.Enum.enumFrom"     == none
#guard valueMap "GHC.Enum.enumFromThen" == none

/-! ## M2 Task 1 — records audit -/

-- AUDIT (examples/haskell/RecordOps.hs → Generated/RecordOps.lean, GHC 9.2.7
-- pass-0000). Hypothesis under test: record construction / update / selectors
-- desugar to plain Core that the transpiler already handles. CONFIRMED at the
-- Core level; the two things that broke were *emission*-level, both fixed below.
--
-- Features exercised and the observed Core spines, verbatim from
-- /tmp/transpile-RecordOps.json (`@ty` = an erased type application; names are
-- `<name>_<unique>` as the shim delivers them):
--
--  1. LABELED CONSTRUCTION `Point { px = x, py = y }` → positional ctor app,
--     labels gone (no field-name residue anywhere in the dump):
--       mkPoint = \x_2144 -> \y_2145 -> ((Point_2301 x_2144) y_2145)
--  2. SELECTORS are ordinary top-level Core defs — one case with one alt, GHC
--     names every binder `ds` (they are `wild`-scrutinised, binder unique 0):
--       px      = \ds_2446 -> (case ds_2446 as wild_0 of
--                               { Point ds_2447 ds_2448 -> ds_2447 })
--       topLeft = \ds_2434 -> (case ds_2434 as wild_0 of
--                               { Rect ds_2435 ds_2436 ds_2437 -> ds_2435 })
--  3. SINGLE-FIELD UPDATE `p { px = px p + d }` → case-and-rebuild. Note the
--     asymmetry: the new-value expression re-reads through the SELECTOR on the
--     ORIGINAL variable (`(px_2136 p_2147)`) and the matching binder `ds_2429`
--     goes unused — GHC does not reuse the case binder for the read:
--       shiftX = \d_2146 -> \p_2147 -> (case p_2147 as wild_0 of
--         { Point ds_2429 ds_2430 ->
--             ((Point_2301 ((((GHC.Num.+_1300 @ty) GHC.Num.$fNumInt_2248)
--                            (px_2136 p_2147)) d_2146)) ds_2430) })
--  4. MULTI-FIELD UPDATE `r { width = w, height = h }` → same case-and-rebuild;
--     here the UNTOUCHED field does come from the case binder (`ds_2424`):
--       resize = \w_2287 -> \h_2288 -> \r_2289 -> (case r_2289 as wild_0 of
--         { Rect ds_2424 ds_2425 ds_2426 -> (((Rect_2319 ds_2424) w_2287) h_2288) })
--  5. SELECTOR AS A FIRST-CLASS FUNCTION `map px ps` → the selector is passed as
--     an ordinary Var; no wrapper, no eta-reduction of `xs` (the type args sit
--     between `map` and its value args):
--       xs = \ps_2290 -> ((((GHC.Base.map_121 @ty) @ty) px_2136) ps_2290)
--     `GHC.Base.map` is the already-mapped key (→ `List.map`), so nothing new.
--  6. Nested record FIELD of user type: `Rect`'s `topLeft :: Point`.
--
-- NEGATIVES worth recording (later M2 tasks rest on them):
--   * TAG CENSUS — every `"tag"` PRESENT in this dump, with counts: TyCon ×177,
--     Var ×78, App ×73, NonRec ×23, Lit ×18, Lam ×14, TyFun ×14, LitWord ×8,
--     Case ×7, DataAlt ×7, Type ×7, LitString ×6, LitInt ×4 (13 distinct tags).
--     ABSENT: `"tag":"Cast"` ×0, `"tag":"Coercion"` ×0, `"tag":"Let"` ×0.
--     Scope of the coercion negative: none of the record shapes in THIS dump
--     produced one, so M2 Task 2's `ECoercion` plumbing is unexercised *here*.
--     That is not a claim about records in general — newtype fields, strict
--     fields and GND-derived selectors are Task 2-3's probes for it.
--     The LitString ×6 and LitWord ×8 sit ENTIRELY in the Typeable binds that
--     `isJunkName` drops: `$trModule` (2 × LitString) and `$tcPoint`/`$tcRect`/
--     `$tc'Point`/`$tc'Rect` (1 × LitString + 2 × LitWord each). No value bind
--     carries either tag.
--   * `.transpile-sandbox/.decls/RecordOps.decls.json` gives BOTH decls
--     `"kind": "data"` (the field Task 4 filters newtypes on), each ctor
--     carrying named `fields` (`topLeft`/`width`/`height`, `px`/`py`) — so
--     record-ness is visible in the sidecar even though Core has erased it.
--   * decls.json order is REVERSE SOURCE ORDER (`Rect` before `Point`) — this
--     is what made the sort below necessary, and it means dump order must never
--     be trusted as dependency order.
--   * No `$sel:`-style selector names and no `tyConOpaque`/`GHC.`/`$c` residue
--     in the generated file; the only `$`-binds in the dump are the
--     `$trModule`/`$tcPoint`/`$tc'Rect`/`$krep` Typeable junk already dropped.
--
-- TWO EMISSION BUGS SURFACED (both loud compile errors, neither silent-wrong):
--
-- (A) DECL ORDER + a local type as another decl's FIELD type. With `Rect`
--     emitted first (dump order) and its field type still opaque in the data
--     block, the output was
--       inductive Rect where | Rect : RecordOps.Point → Int → Int → Rect
--     i.e. `Unknown identifier RecordOps.Point` — two faults at once: the data
--     block never got `resolveUserTypes` (so the field stayed
--     `(GHCCore.tyConOpaque "Point")` and the shared ext-types manifest, which
--     also lists the CURRENT module's types, rewrote it to `RecordOps.Point`),
--     and `Point` was declared after `Rect`. Fix: `sortDataDecls` (dependency
--     order) + `resolveUserTypes` over the data block. Manifest self-entries are
--     now dead rather than removed (that file belongs to Task 4).
-- (B) SPEC-TEXT ctor application to a LITERAL argument. `resolveUserCtors`'s
--     four fixed needles all require a `(` right after the ctor name, so in
--     `Rect (Point 0 0) 1 1` only the outer `Rect` was qualified; the inner
--     `Point 0 0` stayed bare → `Function expected at Point`. Arithmetic never
--     caught this: its spec's ctor args are all parenthesised
--     (`CustomRatio (-numerator r2) (denominator r2)`). Fix: `replaceCtorApps`,
--     a boundary-aware application-position rewrite.
--
-- For every shape the fixtures exercise, fix (B) is loud in both directions —
-- a false positive puts a TERM where a type is expected (`BEq Point.Point`), a
-- false negative leaves a type where a function is expected, both elaboration
-- errors — EXCEPT inside a hand-written string literal, the one silent-rewrite
-- hedge below.
--
-- KNOWN HEDGE (the single non-loud exposure): the rewrite is textual, so a ctor
-- name followed by args inside a hand-written STRING LITERAL in a spec block is
-- rewritten too — `"s = \"Point 1\""` becomes `Point.Point 1` inside the
-- literal. That is pre-existing exposure of the ` Ctor (` needle as well, not
-- new to `replaceCtorApps`. No fixture emits a `LitString` outside the dropped
-- `$tr`/`$tc` binds (6 there, see the census above), and no Haskell string
-- literal can reach the emitter at all — the AIRTIGHT reason is upstream of
-- `valueMap`: the shim DISCARDS string payloads entirely (`shim/Main.hs:291`
-- emits `"value": "<bs>"` for `MachStr`), so a string literal cannot round-trip
-- regardless of what the maps do. (Belt and braces: Core spells the literal
-- `unpackCString# "…"#` and `unpackCString#` has no `valueMap` arm, so outside
-- the `error`/`undefined` spine — where the whole application collapses to
-- `default` — it would emit as a loud unknown identifier anyway. And note the
-- narrower claim: the string TYPE is mapped — `String` is `[Char]` in Core,
-- which `typeConMap` sends to `List Char`. It is literal PRODUCTION that cannot
-- compile today, not String-typed code in general.) So the residual risk is a
-- hand-authored literal in theorem text — rare, and reviewable in the spec
-- block itself.

def pointDecl : DataDecl :=
  {name := "Point", kind := "data",
   ctors := [ {name := "Point",
               fields := [ {name := "px", ty := .tyCon "Int" []},
                           {name := "py", ty := .tyCon "Int" []} ]} ]}

def rectDecl : DataDecl :=
  {name := "Rect", kind := "data",
   ctors := [ {name := "Rect",
               fields := [ {name := "topLeft", ty := .tyCon "Point" []},
                           {name := "width",   ty := .tyCon "Int" []},
                           {name := "height",  ty := .tyCon "Int" []} ]} ]}

-- Fix (B): the exact fixture spec line that failed. Both ctors get qualified —
-- the outer one by the pre-existing ` Ctor (` needle, the inner one only by the
-- new boundary-aware pass.
#guard resolveSpecText [rectDecl, pointDecl] []
         "area (resize w h (Rect (Point 0 0) 1 1)) = w * h"
       == "area (resize w h (Rect.Rect (Point.Point 0 0) 1 1)) = w * h"

-- Boundary NEGATIVES. The first is load-bearing for this fixture specifically:
-- `Point` is a SUBSTRING of `mkPoint`, which appears in four of the five
-- theorems (Arithmetic never tested this — `CustomRatio` is not a substring of
-- `addRatio`/`subRatio`).
#guard replaceCtorApps "Point" "Point.Point" "mkPoint 1 2"     == "mkPoint 1 2"
#guard replaceCtorApps "Point" "Point.Point" "Points 0"        == "Points 0"
#guard replaceCtorApps "Point" "Point.Point" "Point.Point 0 0" == "Point.Point 0 0"  -- idempotent
#guard replaceCtorApps "Point" "Point.Point" "(p : Point) → Int" == "(p : Point) → Int"
#guard replaceCtorApps "Point" "Point.Point" "List Point"      == "List Point"
-- THE negative that documents why `isArgStart` excludes lowercase letters: with
-- a lowercase arm this line becomes `BEq Point.Point where` and every
-- hand-written-Eq fixture (Arithmetic, Ratio) breaks.
#guard replaceCtorApps "Point" "Point.Point" "instance : BEq Point where"
       == "instance : BEq Point where"
-- Accepted (fail-loud) GAP of that same choice: a ctor applied to a bare
-- VARIABLE is left alone → Lean reports "function expected at Point". Not
-- silent-wrong, and no fixture writes this shape.
#guard replaceCtorApps "Point" "Point.Point" "Point x y" == "Point x y"
-- Positives: every occurrence in a string is rewritten, and the bracket/⟨ arms
-- exist (both UNOBSERVED in fixtures so far — kept as hedges).
#guard replaceCtorApps "Point" "Point.Point" "[Point 1 2, Point 3 4]"
       == "[Point.Point 1 2, Point.Point 3 4]"
#guard replaceCtorApps "Point" "Point.Point" "f (Point ⟨1, 2⟩)" == "f (Point.Point ⟨1, 2⟩)"
#guard replaceCtorApps "Point" "Point.Point" "Point (-1) 2" == "Point.Point (-1) 2"
-- Contrast with the line above, pinning the `isArgStart` alphabet exactly: a
-- PARENTHESISED negative argument rewrites (`(` is an arg start), an
-- UNPARENTHESISED one does not (`-` is not) and stays bare — the same
-- documented, fail-loud false negative as `Point x y`, via the full
-- `resolveUserCtors` pipeline so no fixed needle rescues it either.
#guard resolveUserCtors [pointDecl] "px (Point -1 2)" == "px (Point -1 2)"
-- The four pre-existing needles still fire (never remove a hedge): pattern
-- position, transpiler-emitted App position.
#guard resolveUserCtors [pointDecl] "| Point ds_1 ds_2 =>" == "| Point.Point ds_1 ds_2 =>"
#guard resolveUserCtors [pointDecl] "((Point) (x_1)) (y_2)" == "((Point.Point) (x_1)) (y_2)"

-- Fix (A): dependency order over data decls, both input orders.
#guard dataDeclDeps ["Point", "Rect"] rectDecl  == ["Point"]
#guard dataDeclDeps ["Point", "Rect"] pointDecl == []
#guard (sortDataDecls [rectDecl, pointDecl]).map (·.name) == ["Point", "Rect"]
#guard (sortDataDecls [pointDecl, rectDecl]).map (·.name) == ["Point", "Rect"]

-- `dataDeclDeps` must see THROUGH type wrappers — the most load-bearing
-- property of the sort, since a record field is far more often `[Point]` or
-- `Maybe Point` than a bare `Point`. Without it the original forward-reference
-- bug returns (loud, but only after emission). `tyConNames` recurses into
-- `.tyCon` args, so the wrapper itself (`List`/`Maybe`) is also reported —
-- filtered out by `localNames`, which is why these come back as just `Point`.
def rectListDecl : DataDecl :=
  {name := "RectList", kind := "data",
   ctors := [ {name := "RectList",
               fields := [ {name := "pts", ty := .tyCon "List" [.tyCon "Point" []]} ]} ]}
def rectMaybeDecl : DataDecl :=
  {name := "RectMaybe", kind := "data",
   ctors := [ {name := "RectMaybe",
               fields := [ {name := "p", ty := .tyCon "Maybe" [.tyCon "Point" []]} ]} ]}
#guard dataDeclDeps ["Point"] rectListDecl  == ["Point"]
#guard dataDeclDeps ["Point"] rectMaybeDecl == ["Point"]
#guard (sortDataDecls [rectListDecl, pointDecl]).map (·.name) == ["Point", "RectList"]
#guard (sortDataDecls [rectMaybeDecl, pointDecl]).map (·.name) == ["Point", "RectMaybe"]

-- `dataDeclDeps` DEDUPLICATES. Consumers only test membership, so duplicates are
-- harmless today — this pins the docstring's claim so it stays true. Without the
-- `dedup` wrapper this returns `["Point", "Point"]`; every other guard in this
-- block has at most one dependency per decl and so passes either way.
def segDecl : DataDecl :=
  {name := "Seg", kind := "data",
   ctors := [ {name := "Seg",
               fields := [ {name := "a", ty := .tyCon "Point" []},
                           {name := "b", ty := .tyCon "Point" []} ]} ]}
#guard dataDeclDeps ["Point"] segDecl == ["Point"]
#guard (sortDataDecls [segDecl, pointDecl]).map (·.name) == ["Point", "Seg"]

-- A self-recursive decl is NOT a dependency (Lean inductives are self-recursive
-- by construction), so it must not deadlock the sort.
def intListDecl : DataDecl :=
  {name := "IntList", kind := "data",
   ctors := [ {name := "Nil", fields := []},
              {name := "Cons",
               fields := [ {name := "hd", ty := .tyCon "Int" []},
                           {name := "tl", ty := .tyCon "IntList" []} ]} ]}
#guard dataDeclDeps ["IntList"] intListDecl == []
#guard (sortDataDecls [intListDecl]).map (·.name) == ["IntList"]

-- TOTALITY on a dependency CYCLE (mutually recursive records, which would need
-- a Lean `mutual` block): every decl is still emitted, in dump order, so Lean
-- fails loud on the forward reference. A sort that DROPPED a decl would be the
-- one silent-wrong failure mode of this change — this is the pin against it.
def mutADecl : DataDecl :=
  {name := "A", kind := "data",
   ctors := [ {name := "A", fields := [ {name := "getB", ty := .tyCon "B" []} ]} ]}
def mutBDecl : DataDecl :=
  {name := "B", kind := "data",
   ctors := [ {name := "B", fields := [ {name := "getA", ty := .tyCon "A" []} ]} ]}
#guard (sortDataDecls [mutADecl, mutBDecl]).length == 2
#guard (sortDataDecls [mutADecl, mutBDecl]).map (·.name) == ["A", "B"]

-- Totality fallback: pathological inputs (e.g. duplicate names) fall back to
-- dump order rather than dropping decls. The `pending.filter (·.name != d.name)`
-- step removes BOTH same-named decls while placing only one, so without the
-- length check at the end of `sortDataDecls` this returns a single decl and the
-- other is silently gone. GHC cannot emit two decls with one name; the guard is
-- what makes the docstring's "always exactly the input decls" TRUE rather than
-- merely claimed.
def dupDeclA : DataDecl :=
  {name := "Dup", kind := "data",
   ctors := [ {name := "DupA", fields := [ {name := "ax", ty := .tyCon "Int" []} ]} ]}
def dupDeclB : DataDecl :=
  {name := "Dup", kind := "data",
   ctors := [ {name := "DupB", fields := [ {name := "bx", ty := .tyCon "Bool" []} ]} ]}
#guard (sortDataDecls [dupDeclA, dupDeclB]).length == 2
-- …and the fallback hands back the INPUT, so both ctors survive in dump order.
#guard (sortDataDecls [dupDeclA, dupDeclB]).flatMap (·.ctors.map (·.name))
       == ["DupA", "DupB"]

-- Whole-program pin for fix (A), with a manifest entry for the module's OWN
-- type (`Point → RecordOps`) — exactly what transpile.sh passes: the field type
-- must come out BARE (not `RecordOps.Point`), and `Point` must be declared
-- before the `Rect` that uses it.
def recordProg : Program :=
  {binds := [], typeDecls := [rectDecl, pointDecl], instances := []}
-- This guard also pins the INVARIANT "`resolveUserCtors` never runs on the data
-- block" (pipeline step 3 in Emit.lean's Name-resolution post-passes header). The
-- ctor `Rect` shares its type's name, and the `| Ctor ` needle matches the
-- inductive's own constructor line verbatim — so if the ctor pass were ever
-- applied to the data block, this line would come out
-- `| Rect.Rect : Point → …` (and `Point` in field position would become
-- `Point.Point`), splitting into 1 piece instead of 2.
#guard ((emitFullProgram [("Point", "RecordOps")] recordProg).splitOn
          "| Rect : Point → Int → Int → Rect").length == 2
#guard ((emitFullProgram [("Point", "RecordOps")] recordProg).splitOn "RecordOps.Point").length == 1
#guard ((emitFullProgram [("Point", "RecordOps")] recordProg).splitOn "tyConOpaque").length == 1
#guard (((emitFullProgram [("Point", "RecordOps")] recordProg).splitOn "inductive Rect").head!
          |>.splitOn "inductive Point").length == 2

-- BLASTER DATA POINT (from `lake build GhcCoreToLean.Generated.RecordOps` after
-- the two fixes): all FIVE quantified record goals go through on the first try —
-- `mkPoint_px`, `shiftX_moves`, `shiftX_keeps_py`, `resize_area`, and
-- `topLeft_resize` (`px (topLeft (resize w h (Rect (Point 3 4) 1 1))) = 3`, the
-- nested selector-through-update path, which also re-exercises fix (B) on a
-- MULTI-LINE spec) — plus the `decide` list goal `xs_example`. Blaster also
-- FALSIFIES the near-miss variants with real counterexamples (checked:
-- `px (shiftX d (mkPoint x y)) = x` → d := 1; `py (mkPoint x y) = x` → x := 1,
-- y := 0; `area (resize w h (Rect (Point 0 0) 1 1)) = w + h` → w := -1, h := 0;
-- and `px (topLeft (resize w h (Rect (Point 3 4) 1 1))) = 4` → falsified with no
-- variable assignment needed, since it is false for every w and h). So the ✅s
-- are not vacuous: blaster is genuinely modelling construction, update and
-- selection rather than discharging everything by reflexivity.

/-! ## M2 Task 2 — coercion token -/

-- OBSERVATIONS (read out of ghc-dump-core-0.2.1.0 and shim/Main.hs; NOT from a
-- dump — no fixture produces a coercion yet, see the coverage note at the end).
--
--  1. There is NO `Cast` node in ghc-dump's AST at all. `GhcDump/Ast.hs` `Expr'`
--     lists exactly EVar/EVarGlobal/ELit/EApp/ETyLam/ELam/ELet/ECase/ETick/
--     EType/ECoercion, and `GhcDump/Convert.hs:233` is `Cast x _ -> cvtExpr x`
--     — the cast is thrown away, only its body survives. So the shim can only
--     ever see `ECoercion` (`Convert.hs:239`, `Coercion _ -> ECoercion`), and
--     Parse.lean's `"Cast"` arm was never reachable from a real coercion; the
--     one thing that DID reach it was the old shim's own
--     `{"tag":"Cast","expr":{}}`, whose empty `expr` it could not parse (hard
--     abort of the entire dump). Hence: shim now emits `{"tag":"Coercion"}`,
--     and the legacy `"Cast"` arm degrades payload-free shapes to `.coercion`
--     instead of aborting (exact enumeration at the PARSE guards below).
--  2. `ECoercion` carries NO payload (nullary constructor) — there is nothing to
--     round-trip, which is why `Expr.coercion` is an atom rather than wrapping a
--     type or a pair of types.
--  3. COERCION BINDERS arrive with role `.id`, i.e. they are NOT erased today.
--     Chain: `Convert.cvtBinder` (Convert.hs:114-115) branches on `Var.isId`,
--     and a GHC CoVar IS an Id → it emits `Binder{…}`, not `TyBinder{…}`;
--     `cvtIdDetails` (Convert.hs:177) maps `IdInfo.CoVarId{} -> Ast.CoVarId`;
--     `shim/Main.hs` `binderRole` (~line 150) only recognises `DFunId` plus a
--     `$d`/`$f` NAME prefix, so `CoVarId` falls through to `"id"`. Therefore
--     `Lower.isTypeOrDictBinder` says false, `\(co :: a ~R# b) -> …` survives
--     lowering, and `emitExpr` produces `(fun co_N => …)`: a Lean abstraction
--     over a value that does not exist. NOT IMPLEMENTED HERE (would be
--     speculative — no dump exhibits it). Candidate Task 3 fix: teach
--     `binderRole` about `CoVarId` (either `-> "dict"` or a new `"coercion"`
--     role), which makes BOTH `isTypeOrDictBinder` and `isTypeOrDictArg` erase
--     it for free. The guard below pins the Lean-side lowering of a role-`.id`
--     binder as it arrives TODAY; it is INSENSITIVE to the shim-side fix (the
--     role literal is hard-coded here) — the parse-layer tripwire below is what
--     fires when Task 3 changes the shim. And that tripwire covers only ONE of
--     the two candidate fixes: a NEW role string ("coercion") is rejected by
--     `parseVarRole` today, so introducing it flips the tripwire, whereas
--     mapping `CoVarId -> "dict"` reuses a string that already parses and that
--     `isTypeOrDictBinder` already erases — NOTHING Lean-side moves, so this
--     observation must then be re-verified by hand.

-- A Coercion in ARGUMENT position erases like a type/dict arg: `f co` → `f`.
-- `Expr` derives no `BEq` (see the deriving-free mutual block in AST.lean), so
-- these compare emitted strings, like the `headApp`/`maximumApp` guards above.
def coF : Var := {name := "f", unique := 1, ty := .tyCon "Int" [], role := .id}
#guard emitExpr [] [] (Lower.lowerExpr (.app (.var coF) .coercion))
       == emitExpr [] [] (Expr.var coF)
#guard emitExpr [] [] (Lower.lowerExpr (.app (.var coF) .coercion)) == "f_1"
-- …and it is erased, not merely emitted-as-nothing: the residue name is absent.
#guard ((emitExpr [] [] (Lower.lowerExpr (.app (.var coF) .coercion))).splitOn
          "coercionResidue").length == 1

-- A SURVIVING bare coercion must be LOUD. `GHCCore.coercionResidue` is defined
-- NOWHERE (Runtime.lean is namespace `Hs`), exactly like `GHCCore.typeArg`, so
-- the generated file fails to elaborate rather than silently picking a value.
#guard emitExpr [] [] Expr.coercion == "GHCCore.coercionResidue"

-- Coercion BINDER, pinning observation 3: role `.id` ⇒ the lambda SURVIVES.
-- Lean-side lowering ONLY: the role literal is hard-coded below, so this guard
-- cannot notice Task 3's shim fix — the parse-layer tripwire further down can.
def coBinder : Var := {name := "co", unique := 9, ty := .tyCon "~R#" [], role := .id}
#guard emitExpr [] [] (Lower.lowerExpr (.lam coBinder .coercion))
       == "(fun co_9 => GHCCore.coercionResidue)"

-- PARSE (pure, `Except String Expr`, so guard-testable — no IO involved).
def coTyJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "TyCon"), ("name", .str "Int"), ("args", .arr #[])]
def coVarJson : Lean.Json :=
  Lean.Json.mkObj [("name", .str "f"), ("unique", .num 1),
                   ("type", coTyJson), ("role", .str "id")]
-- TRIPWIRE for Task 3: today `parseVarRole` accepts exactly "id"/"tyVar"/"dict"
-- (Parse.lean:13-19), so a var carrying role "coercion" is REJECTED. That
-- function is `private` to Parse.lean, hence pinning it through `parseVar`,
-- whose only other failure modes are shape errors — which is why the positive
-- control on the SAME object with a known role is part of the guard, not
-- decoration: without it this would pass equally well for a typo'd `unique`.
-- If Task 3 introduces a "coercion" role this flips and the M2 Task 2
-- observations above must be revisited. It does NOT fire for the other
-- candidate fix (`CoVarId -> "dict"`), which changes only Haskell and reuses a
-- string Lean already accepts and already erases — see observation 3.
def coRoleVarJson (r : String) : Lean.Json :=
  Lean.Json.mkObj [("name", .str "co"), ("unique", .num 9),
                   ("type", coTyJson), ("role", .str r)]
#guard (match parseVar (coRoleVarJson "coercion") with
        | .ok _ => false | .error _ => true)
#guard (match parseVar (coRoleVarJson "dict") with
        | .ok _ => true  | .error _ => false)

def coercionJson : Lean.Json := Lean.Json.mkObj [("tag", .str "Coercion")]
def legacyCastJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "Cast"), ("expr", Lean.Json.mkObj [])]
-- Note the two levels: the nested `expr` of a `Cast` is an *Expr* object
-- (`{"tag":"Lit", …}`), whose `lit` field is the *Literal* object.
def litExprJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "Lit"),
                   ("lit", Lean.Json.mkObj [("tag", .str "LitInt"), ("value", .num 7)])]
def nestedCastJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "Cast"), ("expr", litExprJson)]
def bogusCastJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "Cast"),
                   ("expr", Lean.Json.mkObj [("tag", .str "Bogus")])]
-- The remaining degrading shapes, so that EVERY case the enumeration below
-- names is pinned by a guard rather than merely asserted: no `expr` field at
-- all, an `expr` that is not an object, and an `expr` object whose `tag` is
-- present but not a string (`legacyCastJson`'s `{}` covers the absent-`tag`
-- case).
def castNoExprJson : Lean.Json := Lean.Json.mkObj [("tag", .str "Cast")]
def castNonObjExprJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "Cast"), ("expr", .num 5)]
def castNonStrTagJson : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "Cast"),
                   ("expr", Lean.Json.mkObj [("tag", .num 5)])]
-- `f <arg>` as the shim would deliver it, for the COMPOSED parse→lower→emit path.
def appCoJson (argJ : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("tag", .str "App"),
                   ("fun", Lean.Json.mkObj [("tag", .str "Var"), ("var", coVarJson)]),
                   ("arg", argJ)]
-- Errors are folded into the string so a parse failure reports WHY, not just "≠".
def parseEmit (j : Lean.Json) : String :=
  match parseExpr j with
  | .ok e    => emitExpr [] [] e
  | .error m => s!"ERR: {m}"
def parseLowerEmit (j : Lean.Json) : String :=
  match parseExpr j with
  | .ok e    => emitExpr [] [] (Lower.lowerExpr e)
  | .error m => s!"ERR: {m}"

#guard parseEmit coercionJson == "GHCCore.coercionResidue"
-- The legacy `{"tag":"Cast","expr":{}}` no longer ABORTS (it used to fail with
-- an "expected tag" error that killed the whole dump); it degrades to the atom.
-- EXACTLY WHICH SHAPES DEGRADE — the single statement of this claim, which
-- Parse.lean's `"Cast"` arm and observation 1 both point at: `expr` missing,
-- `expr` present but not an object, and `expr` an object whose `tag` is absent
-- or not a string. The last two degrade because `getTag` itself errors on them,
-- not via any explicit shape check. This is DELIBERATE, not lenience-by-
-- accident: the `"Cast"` tag has zero producers (observation 1), and a
-- payload-free `Cast` is indistinguishable from a coercion token. A TAGGED
-- `expr` engages the normal parser and stays LOUD — an unknown tag STRING, or a
-- well-formed tag with a bad payload, propagates its error (loud guard below).
#guard parseEmit legacyCastJson == "GHCCore.coercionResidue"
#guard parseEmit castNoExprJson == "GHCCore.coercionResidue"
#guard parseEmit castNonObjExprJson == "GHCCore.coercionResidue"
#guard parseEmit castNonStrTagJson == "GHCCore.coercionResidue"
-- A well-formed TAGGED nested `expr` still parses as `.cast` (transparent in
-- emission) — backwards compatibility for any dump that does carry one.
#guard parseEmit nestedCastJson == "(7 : Int)"
-- …and the loud half: matched on the CONSTRUCTOR, not on the message text, so
-- rewording a parse error does not break this guard.
#guard (match parseExpr bogusCastJson with | .ok _ => false | .error _ => true)
-- COMPOSED path, the guard that piecewise ones cannot replace: parse ∘ lower
-- must erase the argument. `isTypeOrDictArg` has no `.cast` arm, so if Parse
-- ever yielded `.cast .coercion` here instead of a bare `.coercion` the arg
-- would NOT be erased and this would read `(f_1) (GHCCore.coercionResidue)`.
#guard parseLowerEmit (appCoJson coercionJson) == "f_1"
#guard parseLowerEmit (appCoJson legacyCastJson) == "f_1"

-- COVERAGE NOTE: no fixture reaches any of this yet — 0 `"Cast"`/`"Coercion"`
-- tags across all existing dumps, and the Ratio/RecordOps regression exercises
-- none of the lines above (it only proves nothing else broke). These guards are
-- the SOLE coverage of the new path, and they REMAIN so after Task 3: the
-- newtype fixture did NOT trigger it either (0 `Cast`/0 `Coercion` in
-- `NewtypeBasic` too — census in the M2 Task 3 block below), because ghc-dump
-- discards the newtype cast before the shim can see it.

/-! ## M2 Task 3 — newtype observation -/

-- OBSERVATION (examples/haskell/NewtypeBasic.hs → /tmp/transpile-NewtypeBasic.json,
-- GHC 9.2.7 pass-0000). The load-bearing M2 unknown: what shape does newtype
-- wrap/unwrap have at pass-0000 as delivered through ghc-dump?
--
-- ANSWER: BOTH SIDES ARE ALREADY GONE. The three non-Typeable binds, verbatim
-- from the dump in Task 1's house style (`@ty` = an erased type application):
--
--   mkAge_2131   :: Int -> Age         = \n_2135 -> n_2135
--   getAge_2132  :: Age -> Int         = \ds_2348 -> ds_2348
--   addAges_2133 :: Age -> Age -> Age
--     = \a_2137 -> \b_2138 ->
--         ((((GHC.Num.+_1300 @ty) GHC.Num.$fNumInt_2239) (getAge_2132 a_2137))
--          (getAge_2132 b_2138))
--
-- (The other six binds are the `$trModule` / `$tcAge` / `$tc'Age` / `$krep`×3
-- Typeable junk that `isJunkName` drops — same shape as RecordOps.)
--
--  (a) CONSTRUCTION `Age n` → the BARE VALUE `n_2135`. No ctor application, no
--      cast, no coercion, no wrapper of any kind. This is M2 Task 2's
--      observation 1 in action: GHC wraps `n` in a `Cast`, and
--      `GhcDump/Convert.hs:233` (`Cast x _ -> cvtExpr x`) throws the cast away
--      before the shim runs, leaving only the body.
--  (b) PATTERN `getAge (Age n) = n` → NO case at all: `\ds_2348 -> ds_2348`.
--      Not a case on the `Age` ctor, not a `let`. GHC compiles a newtype match
--      to a cast of the scrutinee too, so the same `Convert.hs:233` erasure
--      removes it. (The binder is GHC's `ds`, as with RecordOps' selectors.)
--  (c) COERCION tokens: ZERO of them — see the census.
--  (d) `.transpile-sandbox/.decls/NewtypeBasic.decls.json` (note the `.decls/`
--      subdirectory — the plan's path is stale), verbatim and complete:
--        {"instances":[],"module":"NewtypeBasic","typeDecls":[{"constructors":
--         [{"fields":[{"name":"_","type":{"args":[],"name":"Int","tag":"TyCon"}}],
--          "name":"Age"}],"kind":"newtype","name":"Age"}]}
--      `"kind":"newtype"` is present, exactly the field Task 4 filters on, with
--      one ctor carrying one field. That field's `name` is `"_"` — the decl
--      plugin's placeholder for an UNNAMED field (contrast RecordOps, whose
--      fields carry real labels `px`/`topLeft`). So Task 4's "single ctor's
--      single field" underlying-type lookup yields `Int` here, and its
--      ≠1-ctor / ≠1-field malformed-dump error path is UNEXERCISED by this
--      fixture (`newtype`s cannot have either shape in Haskell, so only a
--      corrupt sidecar reaches it).
--
-- TAG CENSUS — every `"tag"` PRESENT in this dump, with counts: TyCon ×49,
-- App ×32, Var ×28, Lit ×10, NonRec ×9, TyFun ×4, Lam ×4, LitString ×4,
-- LitWord ×4, Type ×3, LitInt ×2 (11 distinct tags).
-- ABSENT: `Cast` ×0, `Coercion` ×0, `Let` ×0, `Case` ×0, `DataAlt` ×0, `Rec` ×0.
--   * `Case` ×0 / `DataAlt` ×0 is result (b) stated as a negative: this dump
--     contains no pattern match anywhere. POSITIONAL CENSUS of the name `Age`,
--     which is what selects the plan's decision rule: 0 occurrences as a `Var`
--     name (the Var names are exactly n, ds, a, b, getAge, $trModule, $tcAge,
--     $krep, GHC.Num.+, GHC.Num.$fNumInt and the GHC.Types Typeable ctors),
--     0 occurrences as a `DataAlt` name, and 11 occurrences as `TyCon "Age"`.
--     Every single `Age` in the Core is a TYPE reference — which is the whole of
--     Task 4's remaining work, and nothing at the value level.
--   * `Cast` ×0 / `Coercion` ×0 CLOSES the newtype half of Task 1's scope
--     sentence ("newtype fields, strict fields and GND-derived selectors are
--     Task 2-3's probes for it"): a monomorphic, non-GND newtype yields neither,
--     because its coercions live only inside `Cast` nodes that never reach the
--     shim. STILL UNPROBED, explicitly not closed: strict fields, GND-derived
--     instances, and coercion VALUES. So M2 Task 2's `ECoercion` plumbing has
--     no fixture coverage still.
--   * `Lam` ×4 = the four value binders (n, ds, a, b), ALL role `"id"`. No
--     `\(co :: a ~R# b) -> …` binder appeared — the direct negative for M2 Task
--     2's observation 3, which is therefore still unexercised. The shim was NOT
--     touched by this task (`binderRole` unchanged, no `CoVarId` arm), so no
--     re-verification of that observation is owed.
--
-- DECISION RULE APPLIED: the plan's FIRST rule — "ghc-dump already erased
-- wrap/unwrap ⇒ nothing to do at value level". Consequently NOTHING was
-- implemented: no shim change, no `dataConMap` arm for `Age`, no program-derived
-- unwrapping-ctor set, `lowerProgram`'s signature untouched. The guards below
-- pin that negative so a later task cannot quietly assume the mechanism exists.

-- The two observed spines, reconstructed exactly as the dump delivers them
-- (uniques included). The EXISTING pipeline already emits identity — there is
-- no newtype-aware step anywhere in it.
def ntN  : Var := {name := "n",  unique := 2135, ty := .tyCon "Int" [], role := .id}
def ntDs : Var := {name := "ds", unique := 2348, ty := .tyCon "Age" [], role := .id}
#guard emitExpr [] [] (Lower.lowerExpr (.lam ntN (.var ntN)))   == "(fun n_2135 => n_2135)"
#guard emitExpr [] [] (Lower.lowerExpr (.lam ntDs (.var ntDs))) == "(fun ds_2348 => ds_2348)"

-- No static-list hack: `Age` is NOT an unwrapping data con. If a later task
-- reaches for the tempting one-line "fix" (adding it beside `I#`/`W#`/`C#`),
-- this fires and forces the program-derived-set question the plan raises.
#guard isUnwrappingDataCon "Age" == false

-- …and no program-derived set was threaded through lowering. A type ascription
-- rather than a `#guard`, because the plan's rule-3 mechanism would change
-- exactly this signature: that change stops this line compiling, forcing the
-- observations above to be re-read first.
example : CoreProgram → CoreProgram := Lower.lowerProgram

-- HEDGE. The whole negative result rests on GHC + ghc-dump doing the erasure
-- for us, so pin what happens if a future compiler/flag combination stops. Both
-- unimplemented positions route through `ctorNames` + `resolveUserCtors`, and
-- Task 4 removed newtypes from BOTH sets, so a surviving newtype ctor now emits
-- as an ordinary unknown reference: `Age_9` (a Var that is no longer a top-level
-- name, hence the `_<unique>` suffix) in value position, bare `| Age …` in
-- pattern position. Neither identifier exists — the `inductive` is suppressed —
-- so both are loud, and no identity arm was invented for either. That is also
-- the concrete reason the plan's "no global `dataConMap` arm" rule costs nothing.
-- RE-POINTED BY TASK 4 (the pre-erasure strings were `(Age.Age) (n_2135)` and
-- `| Age.Age n_2135 =>`, both produced by qualification against a then-emitted
-- `inductive Age`). The `emitDataDecl` guard after them was NOT re-pointed:
-- suppression lives at `emitFullProgram`'s `datas` map, not inside
-- `emitDataDecl`, which still renders any decl it is handed.
def ageNewtypeDecl : DataDecl :=
  {name := "Age", kind := "newtype",
   ctors := [ {name := "Age", fields := [ {name := "_", ty := .tyCon "Int" []} ]} ]}
def ageCtorV : Var := {name := "Age", unique := 9, ty := .tyCon "Age" [], role := .id}
def mkAgeV : Var :=
  {name := "mkAge", unique := 2131,
   ty := .tyFun (.tyCon "Int" []) (.tyCon "Age" []), role := .id}
def hypValueProg : Program :=
  { binds := [.nonRec mkAgeV (.lam ntN (.app (.var ageCtorV) (.var ntN)))],
    typeDecls := [ageNewtypeDecl], instances := [] }
#guard ((emitFullProgram [] hypValueProg).splitOn "(Age_9) (n_2135)").length == 2
def ntWild  : Var := {name := "wild", unique := 0, ty := .tyCon "Age" [], role := .id}
def getAgeV : Var :=
  {name := "getAge", unique := 2132,
   ty := .tyFun (.tyCon "Age" []) (.tyCon "Int" []), role := .id}
def hypPatBody : Expr :=
  .lam ntDs (.case_ (.var ntDs) ntWild (.tyCon "Int" [])
              [.mk (.dataCon "Age") [ntN] (.var ntN)])
def hypPatProg : Program :=
  { binds := [.nonRec getAgeV hypPatBody],
    typeDecls := [ageNewtypeDecl], instances := [] }
#guard ((emitFullProgram [] hypPatProg).splitOn "| Age n_2135 => n_2135").length == 2

-- The DECL side. `emitDataDecl` still reads no `kind` — hand it a newtype and it
-- renders an `inductive` — because Task 4's suppression is a FILTER on the decls
-- reaching it (`emitFullProgram`'s `datas` map), not a case inside it. The Task 4
-- section's emission guard pins the other half: that filter never hands it one.
#guard ((emitDataDecl false false ageNewtypeDecl).splitOn "inductive Age where").length == 2

-- E2E RESOLUTION of the status recorded above: with Task 4's erasure in place
-- `GhcCoreToLean.Generated.NewtypeBasic` builds and `addAges_sum` is `✅ Valid`,
-- which confirms hand-check (i) of error 4's cascade diagnosis.

-- E2E STATUS — `lake build GhcCoreToLean.Generated.NewtypeBasic` FAILS, exactly
-- as the plan stages it. ALL FOUR errors, verbatim, against the generated file
-- (`inductive Age`; `def mkAge (n_2135 : Int) : Age := n_2135`;
-- `def getAge (ds_2348 : Age) : Int := ds_2348`;
-- `def addAges (a_2137 : Age) (b_2138 : Age) : Age := …`):
--
--   19:2  Type mismatch / n_2135 has type Int but is expected to have type Age
--   22:2  Type mismatch / ds_2348 has type Age but is expected to have type Int
--   25:5  failed to synthesize / HAdd Int Int Age
--   27:88 translateType: unexpected sort type
--         Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))
--
-- Errors 1-3 are the type-level `Age` reference and nothing else: the VALUES are
-- already the erased identities the plan wants, and only the SIGNATURES still
-- say `Age`. Note the failure MODE — `inductive Age` elaborates fine, so these
-- are type MISMATCHES, not unknown identifiers.
-- Error 4 (the theorem) is a CASCADE of errors 1-3, not an independent blaster
-- limitation. Checked by hand, three scratch modules: (i) the Task-4-expected
-- shape (`Age` erased, `mkAge`/`getAge` identities on `Int`) → `✅ Valid`;
-- (ii) `Age` KEPT as an inductive with well-typed bodies (`Age.Age n` /
-- `match`) → also `✅ Valid`, so blaster handles the single-field inductive
-- perfectly well; (iii) `Age` kept with `sorry` bodies (standing in for the
-- errored defs, which elaborate to `sorryAx`) → reproduces error 4's message
-- CHARACTER FOR CHARACTER. `sorryAx`'s first explicit argument is a `Type`, and
-- blaster's `translateType` rejects a sort — hence "unexpected sort type".
-- Consequence for Task 4: the erasure is needed to make the emitted VALUES
-- typecheck, NOT to make blaster cope with the inductive.
--
-- One extra Task-4 hazard observed while checking this, currently DORMANT. The
-- shared manifest for this module is `Age\tNewtypeBasic`
-- (`scripts/transpile_graph.py manifest .transpile-sandbox/.decls NewtypeBasic`),
-- yet the generated file says bare `Age`, never `NewtypeBasic.Age`: the
-- self-entry is dead because `resolveUserTypes` and `resolveExternalTypes`
-- consume the SAME needle `(GHCCore.tyConOpaque "Age")` and the user pass runs
-- first (`Emit.lean`, `resolveSpecText`/`emitFullProgram`). The moment Task 4
-- drops newtypes from the user decl set, that entry goes LIVE and rewrites
-- `Age` → `NewtypeBasic.Age` (a type that no longer exists) — which is exactly
-- why Task 4 Step 3's manifest suppression is not optional.

/-! ## M2 Task 4 — newtype erasure -/

-- The pass itself. `resolveNewtypes` rewrites the OPAQUE spelling of a newtype
-- tycon to its underlying type, running after `resolveUserTypes` (whose decl set
-- excludes newtypes precisely so this needle survives) and before
-- `resolveUserCtors`.
#guard resolveNewtypes [("Age", "Int")] "(x : (GHCCore.tyConOpaque \"Age\"))" == "(x : Int)"
-- NO SUBSTRING BLEED: the needle is the whole opaque form, so a name that merely
-- CONTAINS the newtype's name is untouched (the `"` delimiter does the work).
#guard resolveNewtypes [("Age", "Int")] "(GHCCore.tyConOpaque \"Wage\")"
       == "(GHCCore.tyConOpaque \"Wage\")"
-- …and the reverse containment (`Age` a suffix of `Wage`) is equally blocked, so
-- neither direction depends on which name is declared.
#guard resolveNewtypes [("Wage", "Int")] "(GHCCore.tyConOpaque \"Age\")"
       == "(GHCCore.tyConOpaque \"Age\")"
-- Every occurrence in a string is rewritten (a signature mentions the newtype
-- once per argument), and a type with no newtype in it is returned unchanged.
#guard resolveNewtypes [("Age", "Int")]
         "((GHCCore.tyConOpaque \"Age\") → (GHCCore.tyConOpaque \"Age\"))"
       == "(Int → Int)"
#guard resolveNewtypes [] "(x : Int)" == "(x : Int)"

-- EXTRACTION, well-formed branch: one ctor, one field, underlying type as
-- `emitType` renders it. The field NAME is the decl-plugin's `_` placeholder for
-- an unnamed field (M2 Task 3 observation (d)) and is deliberately not read.
#guard newtypeDecls [ageNewtypeDecl] == [("Age", "Int")]
#guard newtypeDecls [pointDecl] == []          -- `kind == "data"` ⇒ never erased
-- (`DataDecl` derives no `BEq`, so the kept set is compared by name.)
#guard (keptTypeDecls [ageNewtypeDecl, pointDecl]).map (·.name) == ["Point"]

-- EXTRACTION, malformed branch. Haskell admits neither shape, so only a corrupt
-- sidecar reaches here; both are left UNERASED, which means `keptTypeDecls` keeps
-- them and every suppression site treats them as ordinary data. That is loud
-- rather than silent: GHC has already erased the value level, so identity bodies
-- against a surviving inductive are type mismatches (exactly the pre-Task-4
-- failure recorded in the Task 3 block above). No `panic!`, no invented recovery.
def badNewtypeTwoCtors : DataDecl :=
  {name := "Bad2", kind := "newtype",
   ctors := [ {name := "B1", fields := [ {name := "_", ty := .tyCon "Int" []} ]},
              {name := "B2", fields := [ {name := "_", ty := .tyCon "Int" []} ]} ]}
def badNewtypeTwoFields : DataDecl :=
  {name := "BadF", kind := "newtype",
   ctors := [ {name := "BadF", fields := [ {name := "_", ty := .tyCon "Int" []},
                                           {name := "_", ty := .tyCon "Bool" []} ]} ]}
def badNewtypeNoFields : DataDecl :=
  {name := "BadN", kind := "newtype", ctors := [ {name := "BadN", fields := []} ]}
#guard newtypeDecls [badNewtypeTwoCtors]  == []
#guard newtypeDecls [badNewtypeTwoFields] == []
#guard newtypeDecls [badNewtypeNoFields]  == []
#guard (keptTypeDecls [badNewtypeTwoCtors, ageNewtypeDecl]).map (·.name) == ["Bad2"]
-- The malformed decl therefore still emits its `inductive` — pre-Task-4 behavior
-- verbatim — while a well-formed newtype beside it is suppressed.
#guard ((emitFullProgram []
          {binds := [], typeDecls := [badNewtypeTwoCtors, ageNewtypeDecl],
           instances := []}).splitOn "inductive Bad2 where").length == 2

-- NESTED underlying type. `emitType` renders `[Int]` by JUXTAPOSITION (`List
-- Int`, unbracketed — see `Maps.parenArg`), and the hole the opaque needle leaves
-- can be an application ARGUMENT, so the substitution must bracket it or
-- `List (GHCCore.tyConOpaque "Ages")` becomes the ill-typed `List List Int`.
#guard emitType (.tyCon "List" [.tyCon "Int" []]) == "List Int"
def agesNewtypeDecl : DataDecl :=
  {name := "Ages", kind := "newtype",
   ctors := [ {name := "Ages",
               fields := [ {name := "_", ty := .tyCon "List" [.tyCon "Int" []] } ]} ]}
#guard newtypeDecls [agesNewtypeDecl] == [("Ages", "List Int")]
#guard resolveNewtypes [("Ages", "List Int")] "(xs : (GHCCore.tyConOpaque \"Ages\"))"
       == "(xs : (List Int))"
#guard resolveNewtypes [("Ages", "List Int")] "(List (GHCCore.tyConOpaque \"Ages\"))"
       == "(List (List Int))"
-- An underlying type `emitType` ALREADY brackets is not double-bracketed
-- (`(Int × Int)`, `(Int → Int)`) — the same closed-set invariant `parenArg` rests on.
#guard emitType (.tyCon "(,)" [.tyCon "Int" [], .tyCon "Int" []]) == "(Int × Int)"
#guard resolveNewtypes [("Pair", "(Int × Int)")] "(p : (GHCCore.tyConOpaque \"Pair\"))"
       == "(p : (Int × Int))"

-- EMISSION MAP: a program whose only type decl is a newtype emits NO inductive
-- for it, and its ctor is not qualified (both halves of the suppression).
#guard ((emitFullProgram [] hypValueProg).splitOn "inductive").length == 1
#guard ((emitFullProgram [] hypValueProg).splitOn "Age.Age").length == 1
-- …and the erasure reaches the SIGNATURE, which is the whole point: `mkAge`'s
-- `Int → Age` becomes `Int → Int`. (The body is the loud `Age_9` hedge above —
-- this guard is about the type, which no longer mentions `Age` at all.)
#guard ((emitFullProgram [] hypValueProg).splitOn "(n_2135 : Int) : Int").length == 2
#guard ((emitFullProgram [] hypValueProg).splitOn "tyConOpaque").length == 1

-- SORT-INPUT CONSTRAINT (the pipeline header's chain, `Point` → `Wrapper`
-- (newtype) → `Q`): the newtype must stay in `sortDataDecls`' input or the
-- `Point`-needs-`Q` edge is lost and `Point` can be emitted before `Q`.
def qDecl : DataDecl :=
  {name := "Q", kind := "data",
   ctors := [ {name := "Q", fields := [ {name := "qv", ty := .tyCon "Int" []} ]} ]}
def wrapperNtDecl : DataDecl :=
  {name := "Wrapper", kind := "newtype",
   ctors := [ {name := "Wrapper", fields := [ {name := "_", ty := .tyCon "Q" []} ]} ]}
def pointWrapDecl : DataDecl :=
  {name := "PointW", kind := "data",
   ctors := [ {name := "PointW", fields := [ {name := "w", ty := .tyCon "Wrapper" []} ]} ]}
-- The sort sees the chain transitively, from the dump order that breaks naively.
#guard (sortDataDecls [pointWrapDecl, wrapperNtDecl, qDecl]).map (·.name)
       == ["Q", "Wrapper", "PointW"]
-- `newtypeSubsts` pre-resolves the underlying string through `resolveUserTypes`:
-- `emitType` gives `(GHCCore.tyConOpaque "Q")` for a LOCAL data type, and pass 1
-- has already run over the text this gets spliced into, so splicing it raw would
-- leave a live needle for `resolveExternalTypes` to rewrite to a nonexistent `M.Q`.
#guard newtypeDecls  [pointWrapDecl, wrapperNtDecl, qDecl]
       == [("Wrapper", "(GHCCore.tyConOpaque \"Q\")")]
#guard newtypeSubsts [pointWrapDecl, wrapperNtDecl, qDecl] == [("Wrapper", "Q")]
-- End to end over the chain: `Q` and `PointW` emit (in dependency order), the
-- newtype does not, `PointW`'s field is the erased `Q`, and no needle survives.
def chainProg : Program :=
  { binds := [], typeDecls := [pointWrapDecl, wrapperNtDecl, qDecl], instances := [] }
#guard ((emitFullProgram [] chainProg).splitOn "inductive").length == 3
#guard ((emitFullProgram [] chainProg).splitOn "inductive Wrapper").length == 1
#guard ((emitFullProgram [] chainProg).splitOn "| PointW : Q → PointW").length == 2
#guard ((emitFullProgram [] chainProg).splitOn "tyConOpaque").length == 1
#guard (emitFullProgram [] chainProg).splitOn "inductive Q where" |>.head!.isEmpty  -- Q first

-- CHAINED NEWTYPES (`newtype A = A B` where `B` is itself a newtype).
-- `newtypeSubsts` saturates the MAP with fuel = #newtypes, so the result is the
-- same for either dump order — a single fold over the source would resolve `A`
-- only when it happened to precede `B`.
def ntBDecl : DataDecl :=
  {name := "NB", kind := "newtype",
   ctors := [ {name := "NB", fields := [ {name := "_", ty := .tyCon "Int" []} ]} ]}
def ntADecl : DataDecl :=
  {name := "NA", kind := "newtype",
   ctors := [ {name := "NA", fields := [ {name := "_", ty := .tyCon "NB" []} ]} ]}
#guard newtypeSubsts [ntADecl, ntBDecl] == [("NA", "Int"), ("NB", "Int")]
#guard newtypeSubsts [ntBDecl, ntADecl] == [("NB", "Int"), ("NA", "Int")]
-- A recursive newtype (`newtype R = R R`) is legal Haskell and has no underlying
-- type to erase to; self-references are excluded from the saturation, so it
-- terminates and leaves the needle in place — loud, not divergent.
def ntRDecl : DataDecl :=
  {name := "R", kind := "newtype",
   ctors := [ {name := "R", fields := [ {name := "_", ty := .tyCon "R" []} ]} ]}
#guard newtypeSubsts [ntRDecl] == [("R", "(GHCCore.tyConOpaque \"R\")")]

-- SPEC TEXT (pass site 3): the transpiler-emitted opaque form erases there too,
-- while a hand-written `Age` in theorem text is NOT rewritten — properties on a
-- newtype are written against the underlying type, and anything else fails loud.
#guard resolveSpecText [ageNewtypeDecl] [] "(a : (GHCCore.tyConOpaque \"Age\")) → Int"
       == "(a : Int) → Int"
#guard resolveSpecText [ageNewtypeDecl] [] "∀ (a : Age), getAge (mkAge a) = a"
       == "∀ (a : Age), getAge (mkAge a) = a"
-- The ext-types manifest carries no entry for an erased newtype
-- (`scripts/transpile_graph.py` skips `kind == "newtype"`), but even if a stale
-- one is passed in, pass 2 has already consumed the needle — this pins that the
-- self-entry hazard recorded in the Task 3 block is closed at BOTH ends.
#guard resolveSpecText [ageNewtypeDecl] [("Age", "NewtypeBasic")]
         "(a : (GHCCore.tyConOpaque \"Age\")) → Int"
       == "(a : Int) → Int"

-- ZERO CHURN for newtype-free programs: with no newtype decl, `newtypeSubsts` is
-- empty and every pass is the identity it was before Task 4.
#guard newtypeSubsts [pointDecl, rectDecl] == []
#guard resolveSpecText [rectDecl, pointDecl] []
         "area (resize w h (Rect (Point 0 0) 1 1)) = w * h"
       == "area (resize w h (Rect.Rect (Point.Point 0 0) 1 1)) = w * h"

/-! ## M2 Task 5 — newtype-instance loud-fail guard -/

-- ANY instance MENTIONING a newtype anywhere in its head types — head position or
-- nested in an argument — is REFUSED (loud): erasure cannot
-- represent it, and derived-vs-hand-written is indistinguishable in `tcg_insts`
-- (GND instances carry no `$c` methods to sniff). Relaxable later via a
-- decl-plugin origin dump.
--
-- OBSERVED at HEAD before this guard existed — both shapes built with ZERO
-- diagnostics, which is why the guard is soundness-critical and not a
-- representability nicety:
--
--   (a) `newtype Mod7 = Mod7 Int` + hand-written `Eq Mod7` (`a mod 7 == b mod 7`)
--       emitted, inside `namespace Mod7Probe`:
--         instance : BEq Int where
--           beq := _dollar_c_eq__eq__3186     -- the mod-7 function
--       i.e. the Eq RELOCATED onto `Int`. Canary: `example : ((1 : Int) == 8) =
--       false := by decide` → "Tactic `decide` proved that the proposition
--       (1 == 8) = false is false". Every `==` on Int in the module — theorem text
--       included — silently meant mod-7.
--   (b) `newtype Coin = Coin Int` + `instance Ord Coin where compare (Coin a)
--       (Coin b) = compare b a` (REVERSED) emitted no Ord anything: `ordTypes`
--       matched the opaque head so `isSuppressedMethod` dropped all nine `$c`
--       defs, and the newtype was filtered out of `datas` so no `deriving Ord`
--       replaced them. `richer a b = a > b` came out as
--       `(fun a b => decide (a > b))` on plain Int — the OPPOSITE order from the
--       Haskell, with the user's `compare` nowhere in the file.
--
--   (c) `newtype Celsius = Celsius Int` + `instance Eq (Celsius, Celsius)` —
--       ARGUMENT position, which the FIRST version of this guard (head-tycon only)
--       still let through. See the argument-position block below for the observed
--       output and the false theorem it made provable.
--
-- All three are silent-wrong; the guard now makes them exit 1 before anything is
-- written. `examples/haskell/NewtypeInstances.hs` is the committed negative
-- fixture (excluded from the green-regression list).

def eqAgeInst : Instance :=
  {className := "Eq", headTypes := [.tyCon "Age" []], dfunName := "$fEqAge", dfunUnique := 0}
def eqPointInst : Instance :=
  {className := "Eq", headTypes := [.tyCon "Point" []], dfunName := "$fEqPoint", dfunUnique := 0}

-- A violation is detected…
#guard newtypeInstanceViolations [eqAgeInst] [ageNewtypeDecl] == [("Eq", "Age")]
-- …and an instance on a DATA type is not flagged (the guard must not over-fire:
-- `Arithmetic`'s hand-written `Eq CustomRatio` has to keep working).
#guard newtypeInstanceViolations [eqPointInst] [ageNewtypeDecl, pointDecl] == []
-- ZERO CHURN: a newtype-free decl set, and an instance-free program, are both `[]`.
#guard newtypeInstanceViolations [eqPointInst] [pointDecl, rectDecl] == []
#guard newtypeInstanceViolations [] [ageNewtypeDecl] == []

-- KEYED OFF ALL NEWTYPE DECLS, not the erased-pair list: a MALFORMED newtype does
-- not erase (`newtypeDecls` skips it, `keptTypeDecls` keeps it) yet an instance on
-- it is just as unrepresentable — GHC has still erased its value level — so it is
-- still refused. `newtypeNames` is the key, deliberately not `newtypeDecls`.
#guard newtypeDecls [badNewtypeTwoCtors] == []
#guard newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "Bad2" []],
           dfunName := "$fEqBad2", dfunUnique := 0}]
         [badNewtypeTwoCtors] == [("Eq", "Bad2")]
#guard newtypeNames [ageNewtypeDecl, pointDecl, badNewtypeTwoCtors] == ["Age", "Bad2"]

-- EVERY head type is scanned, not just `headTypes.head?`: a multi-parameter class
-- whose SECOND parameter is the newtype is equally unrepresentable.
#guard newtypeInstanceViolations
         [{className := "Convert", headTypes := [.tyCon "Int" [], .tyCon "Age" []],
           dfunName := "$fConvertIntAge", dfunUnique := 0}]
         [ageNewtypeDecl] == [("Convert", "Age")]
-- Ord — shape (b) above, the silently-DROPPED one — is caught by the same rule;
-- nothing about the guard is Eq-specific, and both instances of a two-instance
-- type are reported.
#guard newtypeInstanceViolations
         [{className := "Ord", headTypes := [.tyCon "Age" []],
           dfunName := "$fOrdAge", dfunUnique := 0}, eqAgeInst]
         [ageNewtypeDecl] == [("Ord", "Age"), ("Eq", "Age")]

-- ARGUMENT POSITION, formerly a recorded scope limit and in fact SILENT-WRONG:
-- head-only detection read `instance Eq (Maybe Age)` as head `Maybe` and let it
-- through. Detection is now STRUCTURAL, so a newtype nested anywhere in a head
-- type is flagged.
--
-- OBSERVED on the pre-fix binary (`f323c5f`), the reason this is a soundness fix
-- and not a completeness nicety. `newtype Celsius = Celsius Int` +
-- `instance {-# OVERLAPPING #-} Eq (Celsius, Celsius) where
--    (Celsius a, _) == (Celsius b, _) = a == b`
-- transpiled with exit 0 and EMPTY stderr, emitting inside the module namespace:
--     def _dollar_c_eq__eq__3286 (ds_3425 : (Int × Int)) (ds_3426 : (Int × Int)) : Bool := …
--     instance : BEq (Int × Int) where
--       beq := _dollar_c_eq__eq__3286        -- compares FIRST COMPONENTS ONLY
-- i.e. Eq relocated onto `Int × Int`, so
--     theorem _ : (((1,2) : Int × Int) == ((1,3) : Int × Int)) = true := by decide
-- BUILT (`lake build` succeeded). Every `==` on a pair of Ints in the module,
-- theorem text included, silently meant "first components equal".
--
-- The shape below is exactly what the shim dumps for that head:
-- `.tyCon "(,)" [.tyCon "Celsius" [], .tyCon "Celsius" []]` — unqualified inner
-- names, matching `newtypeNames`. Reported ONCE despite two mentions (dedup).
#guard newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "(,)" [.tyCon "Age" [], .tyCon "Age" []]],
           dfunName := "$fEq(,)", dfunUnique := 0}]
         [ageNewtypeDecl] == [("Eq", "Age")]
-- …the `Maybe`-argument shape that the old comment pinned as UNFLAGGED.
#guard newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "Maybe" [.tyCon "Age" []]],
           dfunName := "$fEqMaybeAge", dfunUnique := 0}]
         [ageNewtypeDecl] == [("Eq", "Age")]
-- …either side of a function arrow (`instance C (Age -> Int)`, `instance C (Int -> Age)`)…
#guard newtypeInstanceViolations
         [{className := "C", headTypes := [.tyFun (.tyCon "Age" []) (.tyCon "Int" [])],
           dfunName := "$fC", dfunUnique := 0}]
         [ageNewtypeDecl] == [("C", "Age")]
#guard newtypeInstanceViolations
         [{className := "C", headTypes := [.tyFun (.tyCon "Int" []) (.tyCon "Age" [])],
           dfunName := "$fC", dfunUnique := 0}]
         [ageNewtypeDecl] == [("C", "Age")]
-- …either side of a curried `.tyApp` (the un-saturated dump shape)…
#guard newtypeInstanceViolations
         [{className := "C", headTypes := [.tyApp (.tyCon "Maybe" []) (.tyCon "Age" [])],
           dfunName := "$fC", dfunUnique := 0}]
         [ageNewtypeDecl] == [("C", "Age")]
-- …and under a `∀`.
#guard newtypeInstanceViolations
         [{className := "C", headTypes := [.forAll "a" (.tyCon "Maybe" [.tyCon "Age" []])],
           dfunName := "$fC", dfunUnique := 0}]
         [ageNewtypeDecl] == [("C", "Age")]
-- NO OVER-FIRE: a DATA type in each of those same positions is still fine. This
-- is what keeps `Hs.splitAt`-style pair types and `Arithmetic`'s hand-written
-- `Eq CustomRatio` working — the recursion must be newtype-keyed, not tuple-shy.
#guard newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "(,)" [.tyCon "Point" [], .tyCon "Point" []]],
           dfunName := "$fEq(,)", dfunUnique := 0}]
         [ageNewtypeDecl, pointDecl] == []
#guard newtypeInstanceViolations
         [{className := "Eq", headTypes := [.tyCon "Maybe" [.tyCon "Point" []]],
           dfunName := "$fEqMaybePoint", dfunUnique := 0}]
         [ageNewtypeDecl, pointDecl] == []
#guard newtypeInstanceViolations
         [{className := "C", headTypes := [.tyFun (.tyCon "Point" []) (.tyCon "Int" [])],
           dfunName := "$fC", dfunUnique := 0}]
         [ageNewtypeDecl, pointDecl] == []
-- Type VARIABLES and type LITERALS are not names to match against either.
#guard newtypeInstanceViolations
         [{className := "C", headTypes := [.tyCon "Maybe" [.tyVar "Age"], .tyLit (.nat 7)],
           dfunName := "$fC", dfunUnique := 0}]
         [ageNewtypeDecl] == []

-- DEDUP is per (class, newtype) PAIR, not per newtype: a head mentioning the same
-- newtype twice reports once (above), while two DIFFERENT newtypes in one head
-- still report both, in dump order.
#guard newtypeInstanceViolations
         [{className := "Convert",
           headTypes := [.tyCon "(,)" [.tyCon "Age" [], .tyCon "Bad2" []]],
           dfunName := "$fConvert", dfunUnique := 0}]
         [ageNewtypeDecl, badNewtypeTwoCtors] == [("Convert", "Age"), ("Convert", "Bad2")]

-- ORPHAN INSTANCES (was a recorded scope limit here; CLOSED by Task 6, which had
-- to close it — see that section for the observed refusal). With no local decls
-- and no imported-newtype names, the newtype set is empty and nothing is reported:
-- this pins that the empty-set path is total (no crash).
#guard newtypeInstanceViolations [eqAgeInst] [] == []
-- The loudness of THAT configuration rests on the needle surviving into the
-- generated Lean, where `GHCCore.tyConOpaque` is undefined (nothing in
-- `GhcCoreToLean/Runtime.lean` declares it). Task 6 OBSERVED that failure verbatim
-- for a newtype the manifest cannot carry:
--   error: …/NtUserUnderClient.lean:13:23: Unknown identifier `GHCCore.tyConOpaque`
-- But once the manifest DOES carry the newtype, the needle is erased and the same
-- input would silently relocate the instance — so the guard now takes the imported
-- names too (Task 6 section).

-- The message names the class, the newtype, the underlying type and the remedy.
#guard ((newtypeInstanceError [ageNewtypeDecl] ("Eq", "Age")).splitOn "instance Eq Age").length == 2
#guard ((newtypeInstanceError [ageNewtypeDecl] ("Eq", "Age")).splitOn
         "underlying type `Int`").length == 2
-- …and degrades honestly for a malformed newtype, which has no underlying type to
-- name (the `newtypeSubsts` lookup misses).
#guard ((newtypeInstanceError [badNewtypeTwoCtors] ("Eq", "Bad2")).splitOn
         "malformed dump").length == 2

-- MALFORMED-NEWTYPE diagnostic (WARNING, not error — Haskell admits neither
-- shape, so only a corrupt sidecar reaches it, and the downstream Lean type
-- mismatch is already loud; erroring would newly refuse input that transpiles).
#guard malformedNewtypes [ageNewtypeDecl, pointDecl] == []
#guard malformedNewtypes
         [badNewtypeTwoCtors, badNewtypeTwoFields, badNewtypeNoFields, ageNewtypeDecl]
       == ["Bad2", "BadF", "BadN"]
#guard ((malformedNewtypeWarning "Bad2").splitOn "Bad2").length == 2
#guard ((malformedNewtypeWarning "Bad2").splitOn "FAIL to typecheck").length == 2

/-! ## M2 Task 6 — cross-module records & newtypes (`RecordClient.hs`) -/

-- OBSERVED (`/tmp/transpile-RecordClient.json`, GHC 9.2.7 pass-0000, module
-- importing `RecordOps (Point, mkPoint, px)` + `NewtypeBasic (Age, mkAge, getAge)`):
--
--   (a) An imported newtype in a SIGNATURE arrives as a BARE tycon, the same
--       convention imported `data` types use (Task 1's observation for `Point`):
--         "binder": {"name":"bumpAge", …
--           "type":{"arg":{"args":[],"name":"Age","tag":"TyCon"},
--                   "res":{"args":[],"name":"Age","tag":"TyCon"},"tag":"TyFun"}}
--       compare the imported data type, same dump:
--           {"arg":{"args":[],"name":"Point","tag":"TyCon"}, …}   -- originDist
--       So `emitType` produces the SAME `(GHCCore.tyConOpaque "Age")` needle a
--       local newtype would, and the client's `typeDecls` is `[]` (the decl plugin
--       dumps only `tcg_tcs`), which is why pass 2 needs the manifest channel.
--
--   (b) PLAN CORRECTION. The plan's Step 2 expected `clientAge`'s Core type to
--       carry `Age`. It does NOT: `clientAge :: Int -> Int` dumps as
--           "type":{"arg":{…"name":"Int"…},"res":{…"name":"Int"…},"tag":"TyFun"}
--       and the value level is already GHC-erased, so that function transpiled and
--       verified (`✅ Valid`) even BEFORE this task — it proves the value half of
--       cross-module newtype use, not the type half. `bumpAge :: Age -> Age` was
--       added to the fixture as the function that actually reaches the type level;
--       without it the fixture never touches the gap the task exists to close.
--
--   (c) NEW LIMITATION observed (records half, not newtypes). Imported VALUE names
--       in `@lean` spec text are NOT qualified — only types are (pass 4 rewrites
--       type needles; nothing rewrites a bare function name). The plan's
--       `theorem originDist_mk : … originDist (mkPoint x y) = x` failed loud:
--           error: RecordClient.lean:22:51: Function expected at
--             mkPoint
--           but this term has type ?m.1
--       Fixed IN THE FIXTURE by writing `RecordOps.mkPoint`. Same family as the
--       bare-ctor-application limitation Task 7's README bullet already covers;
--       imported selectors used in DEFS (`px` → `RecordOps.px`) are unaffected —
--       those come from Core, where the name arrives qualified.
--
--   (d) PLAN CORRECTION. The plan's Step 1 expected the manifest to carry `Point`
--       but NOT `Age` ("a newtype has no Lean name to qualify"). It now carries
--       `Age⇥newtype⇥Int` as well: the plan predates the two-CHANNEL design, under
--       which the newtype line publishes the UNDERLYING type rather than a module
--       to qualify with. The plan's claim is still true of the DATA channel —
--       `scripts/transpile_graph.py manifest` skips newtypes, and it is the
--       defining module's own transpile that appends the newtype line.

-- EXPORT SET. `newtypeExports` publishes a newtype iff its underlying string is
-- built entirely from `typeConMap`-mapped tycons, which is exactly "contains no
-- `GHCCore.tyConOpaque` needle". Builtin and mapped-compound underlyings export…
#guard newtypeExports [ageNewtypeDecl]  == [("Age", "Int")]
#guard newtypeExports [agesNewtypeDecl] == [("Ages", "List Int")]
-- …and the export is the RAW `emitType` form (`List Int`, unbracketed): the
-- consumer's `resolveNewtypes` re-applies `newtypeArg`, so bracketing exactly once
-- keeps argument position right on the client side too.
#guard resolveNewtypes [("Ages", "List Int")] "(List (GHCCore.tyConOpaque \"Ages\"))"
       == "(List (List Int))"
-- A newtype over a LOCAL user type is SKIPPED (documented M2 limitation): the
-- correct spelling in a client is `M.Q`, which needs qualified-underlying
-- resolution. Note the test must read the PRE-`resolveUserTypes` string —
-- `newtypeSubsts` has already turned the needle into a bare `Q` by then, which is
-- why the filter runs on `newtypeChainSubsts`.
#guard newtypeSubsts [wrapperNtDecl, qDecl] == [("Wrapper", "Q")]
#guard newtypeChainSubsts [wrapperNtDecl, qDecl]
       == [("Wrapper", "(GHCCore.tyConOpaque \"Q\")")]
#guard newtypeExports [wrapperNtDecl, qDecl] == []
-- A newtype over an IMPORTED/unknown user type is skipped by the same rule (`Point`
-- is not among the decls here, so nothing resolves it away either). This is the
-- probe fixture's `newtype WrapP = WrapP Point`, reconstructed.
def wrapPNtDecl : DataDecl :=
  {name := "WrapP", kind := "newtype",
   ctors := [ {name := "WrapP", fields := [ {name := "_", ty := .tyCon "Point" []} ]} ]}
#guard newtypeExports [wrapPNtDecl] == []
-- The recursive newtype is skipped too — its needle is its own name.
#guard newtypeExports [ntRDecl] == []
-- CHAINS export once flattened to a mapped type, in either dump order, and a
-- malformed newtype exports nothing (`newtypeDecls` never lists it).
#guard newtypeExports [ntADecl, ntBDecl] == [("NA", "Int"), ("NB", "Int")]
#guard newtypeExports [ntBDecl, ntADecl] == [("NB", "Int"), ("NA", "Int")]
#guard newtypeExports [badNewtypeTwoCtors, badNewtypeTwoFields, badNewtypeNoFields] == []
-- ZERO CHURN: a newtype-free module publishes nothing (the sidecar is written but
-- empty, so `transpile.sh` appends nothing).
#guard newtypeExports [pointDecl, rectDecl] == []

-- MANIFEST FORMAT. Data lines are byte-identical to what they always were; the
-- newtype channel is a third field behind the `newtype` tag.
#guard newtypeManifestLine "Age" "Int" == "Age\tnewtype\tInt"
#guard parseExtManifest "Point\tRecordOps\nRect\tRecordOps\n"
       == {datas := [("Point", "RecordOps"), ("Rect", "RecordOps")]}
#guard parseExtManifest "Age\tnewtype\tInt\n" == {newtypes := [("Age", "Int")]}
-- Both channels in one file, in file order, kept DISJOINT — a newtype leaking into
-- the data channel would emit the nonexistent `newtype.Age`. This is the exact
-- content `transpile.sh` produced for `RecordClient`.
#guard parseExtManifest "Rect\tRecordOps\nPoint\tRecordOps\nAge\tnewtype\tInt\n"
       == {datas := [("Rect", "RecordOps"), ("Point", "RecordOps")],
           newtypes := [("Age", "Int")]}
-- An underlying type may contain SPACES but never a tab, so the 3-field split is
-- unambiguous for compound types.
#guard parseExtManifest "Ages\tnewtype\tList Int\n" == {newtypes := [("Ages", "List Int")]}
#guard parseExtManifest "Pair\tnewtype\t(Int × Int)\n" == {newtypes := [("Pair", "(Int × Int)")]}
-- MALFORMED lines are REJECTED (the caller warns) and dropped, never guessed at.
-- Dropping is the safe failure: the un-erased needle is loud at `lake build`.
#guard parseExtManifest "Age\n"                == {rejected := ["Age"]}
#guard parseExtManifest "\tRecordOps\n"        == {rejected := ["\tRecordOps"]}
#guard parseExtManifest "Point\t\n"            == {rejected := ["Point\t"]}
#guard parseExtManifest "Age\tnewtype\t\n"     == {rejected := ["Age\tnewtype\t"]}
#guard parseExtManifest "Age\tnewtype\tInt\tX\n" == {rejected := ["Age\tnewtype\tInt\tX"]}
#guard parseExtManifest "Age\tdata\tInt\n"     == {rejected := ["Age\tdata\tInt"]}
-- A TRUNCATED newtype line is rejected, NOT read as data — this is what makes
-- "the channels cannot collide" true at the parser and not only at the writers
-- (as data it would rewrite `Age` → `newtype.Age`).
#guard parseExtManifest "Age\tnewtype\n"       == {rejected := ["Age\tnewtype"]}
-- Empty lines (every file ends with one) are neither parsed nor reported, and a
-- good line beside a bad one still lands.
#guard parseExtManifest "" == {}
#guard parseExtManifest "\n\n" == {}
#guard parseExtManifest "Point\tRecordOps\nAge\n"
       == {datas := [("Point", "RecordOps")], rejected := ["Age"]}
-- AMBIGUITY. Two manifest configurations would be SILENT-wrong rather than loud,
-- so both are refused rather than resolved. Both drop ALL of the name's entries —
-- the reference stays opaque and fails loud — and report the name for the caller
-- to warn about.
--
-- (1) CROSS-CHANNEL: with `data Age` in module B and `newtype Age = Age Int` in
-- module A, a client using B's Age would have it ERASED to `Int` by pass 2 (which
-- runs before pass 4), and a theorem over `Int` typechecks.
#guard parseExtManifest "Age\tB\nAge\tnewtype\tInt\n" == {ambiguous := ["Age"]}
#guard parseExtManifest "Age\tnewtype\tInt\nAge\tB\n" == {ambiguous := ["Age"]}
-- Unrelated entries in the same file are unaffected, and the report is deduped.
#guard parseExtManifest "Point\tRecordOps\nAge\tB\nAge\tnewtype\tInt\nAge\tnewtype\tBool\n"
       == {datas := [("Point", "RecordOps")], ambiguous := ["Age"]}
-- (2) WITHIN THE NEWTYPE CHANNEL with DIFFERENT underlyings — verified silent-wrong
-- on a live 3-module probe before this check existed: `A: newtype Key = Key Int`,
-- `B: newtype Key = Key [Int]`, client importing B's `Key`. `resolveNewtypes` folds
-- left, so the client emitted `idKey : Int → Int` for a `[Int] -> [Int]` function
-- and `∀ (k : Int), idKey k = k` reported `✅ Valid`, with zero diagnostics. Refused
-- in EITHER dump order (which one comes first is dependency order, not a property
-- of the clash).
#guard parseExtManifest "Key\tnewtype\tInt\nKey\tnewtype\tList Int\n"
       == {ambiguous := ["Key"]}
#guard parseExtManifest "Key\tnewtype\tList Int\nKey\tnewtype\tInt\n"
       == {ambiguous := ["Key"]}
-- All THREE entries go, not just the two that disagree, and neighbours survive.
#guard parseExtManifest "Point\tRecordOps\nKey\tnewtype\tInt\nAge\tnewtype\tInt\nKey\tnewtype\tBool\n"
       == {datas := [("Point", "RecordOps")], newtypes := [("Age", "Int")],
           ambiguous := ["Key"]}
-- The SAME underlying published by two modules is NOT a clash: the entries say the
-- same thing, so they DEDUP to one and nothing is refused. (This is the reachable
-- benign case — re-exported/duplicated newtype definitions across a graph.)
#guard parseExtManifest "Key\tnewtype\tInt\nKey\tnewtype\tInt\n"
       == {newtypes := [("Key", "Int")]}
#guard parseExtManifest "Key\tnewtype\tInt\nAge\tnewtype\tBool\nKey\tnewtype\tInt\n"
       == {newtypes := [("Key", "Int"), ("Age", "Bool")]}
-- MIXED: a cross-channel clash on one name and a distinct-underlying clash on
-- another, in one file — both names are reported, in file order.
#guard parseExtManifest "Age\tB\nAge\tnewtype\tInt\nKey\tnewtype\tInt\nKey\tnewtype\tBool\n"
       == {ambiguous := ["Age", "Key"]}
-- The SAME name twice in the DATA channel is NOT refused (first entry wins, as it
-- always has): there the consequence is a mis-qualified `WrongModule.Point`, which
-- is loud, so no silent-wrong path needs closing. That asymmetry is the whole
-- reason the newtype channel is treated more strictly than the data one.
#guard parseExtManifest "Point\tA\nPoint\tB\n" == {datas := [("Point", "A"), ("Point", "B")]}
#guard resolveExternalTypes [("Point", "A"), ("Point", "B")] "(GHCCore.tyConOpaque \"Point\")"
       == "A.Point"

-- SUBSTITUTION SLOT. Imported newtypes are erased at PASS 2, from `extNts`. This
-- is the client's exact emitted signature shape: no local decls at all, the needle
-- erased to `Int`, and no `tyConOpaque` left for pass 4 to turn into a
-- `NewtypeBasic.Age` that does not exist.
def clientBumpV : Var :=
  {name := "bumpAge", unique := 4002,
   ty := .tyFun (.tyCon "Age" []) (.tyCon "Age" []), role := .id}
def clientA : Var := {name := "a", unique := 4002, ty := .tyCon "Age" [], role := .id}
def clientProg : Program :=
  { binds := [.nonRec clientBumpV (.lam clientA (.var clientA))],
    typeDecls := [], instances := [] }
#guard ((emitFullProgram [] clientProg [("Age", "Int")]).splitOn
         "(a_4002 : Int) : Int").length == 2
#guard ((emitFullProgram [] clientProg [("Age", "Int")]).splitOn "tyConOpaque").length == 1
-- Without the channel the needle SURVIVES — the pre-Task-6 state, loud at `lake
-- build` (`Unknown identifier GHCCore.tyConOpaque`), never silent.
#guard ((emitFullProgram [] clientProg []).splitOn "tyConOpaque").length == 3
-- Pass 4 must NOT see the needle: with a (hypothetical, python-suppressed) data
-- entry for `Age` present as well, the newtype channel still wins because pass 2
-- runs first. Both directions of the manifest hazard are now pinned.
#guard ((emitFullProgram [("Age", "NewtypeBasic")] clientProg [("Age", "Int")]).splitOn
         "NewtypeBasic.Age").length == 1
-- LOCAL SHADOWING: a local newtype of the same bare name wins over the imported
-- entry (local substitutions are prepended, and the first match consumes the
-- needle). The manifest's keys are unqualified, so this rule has to be stated.
#guard ((emitFullProgram [] {clientProg with typeDecls := [ageNewtypeDecl]}
          [("Age", "Bool")]).splitOn "(a_4002 : Int) : Int").length == 2
-- SPEC TEXT (pass site 3) takes the same channel, so a theorem about an imported
-- newtype-typed function elaborates against the underlying type.
#guard resolveSpecText [] [] "(a : (GHCCore.tyConOpaque \"Age\")) → Int" [("Age", "Int")]
       == "(a : Int) → Int"
-- ZERO CHURN for every existing call site: `extNts` defaults to `[]`, and with it
-- empty both passes are exactly the pre-Task-6 identity.
#guard emitFullProgram [] clientProg == emitFullProgram [] clientProg []
#guard resolveSpecText [ageNewtypeDecl] [] "(a : (GHCCore.tyConOpaque \"Age\")) → Int"
       == resolveSpecText [ageNewtypeDecl] [] "(a : (GHCCore.tyConOpaque \"Age\")) → Int" []

-- THE SOUNDNESS COUPLING (why this task had to touch Task 5's guard). Erasing an
-- imported newtype's needle makes an ORPHAN instance on it silent-wrong — exactly
-- Task 5 failure mode (a), now reachable from a module whose `typeDecls` is empty.
-- What the emitter WOULD produce, pinned so the coupling cannot be re-broken: a
-- client-side `$c==` on the imported newtype plus the orphan instance, i.e. the
-- shape `NtOrphanProbe.hs` dumps.
def eqAgeMethodV : Var :=
  {name := "$c==", unique := 3186,
   ty := .tyFun (.tyCon "Age" []) (.tyFun (.tyCon "Age" []) (.tyCon "Bool" [])),
   role := .id}
def clientB : Var := {name := "b", unique := 4003, ty := .tyCon "Age" [], role := .id}
def orphanEqProg : Program :=
  { binds := [.nonRec eqAgeMethodV (.lam clientA (.lam clientB (.var clientB)))],
    typeDecls := [], instances := [eqAgeInst] }
#guard ((emitFullProgram [] orphanEqProg [("Age", "Int")]).splitOn "BEq Int").length == 2
-- So the guard takes the IMPORTED names too, and reports the same violation it
-- would for a local decl…
#guard newtypeInstanceViolations [eqAgeInst] [] ["Age"] == [("Eq", "Age")]
-- …with an honest underlying type in the message (the local `newtypeSubsts` lookup
-- cannot find an imported newtype, so `extNts` is consulted as well — otherwise
-- the message would claim the dump is malformed).
#guard ((newtypeInstanceError [] ("Eq", "Age") [("Age", "Int")]).splitOn
         "underlying type `Int`").length == 2
#guard ((newtypeInstanceError [] ("Eq", "Age")).splitOn "malformed dump").length == 2
-- INVARIANT (Emit's guard-section header): the guard's name set ⊇ the set pass 2
-- erases. Cross-module both sides read the same channel, so for any manifest the
-- one is the other's key list.
#guard (newtypeExports [ageNewtypeDecl]).map (·.1) == ["Age"]
-- NO OVER-FIRE from the new parameter: an instance on a local DATA type is still
-- fine while imported newtype names are in scope.
#guard newtypeInstanceViolations [eqPointInst] [pointDecl] ["Age"] == []
-- …and an imported newtype the manifest did NOT carry (skip rule) is invisible to
-- the guard, unchanged from Task 5 — and still loud downstream, since nothing
-- erased its needle either. OBSERVED end-to-end (probe modules, not committed):
--   `newtype WrapP = WrapP Point` (Point imported) → sidecar EMPTY, no manifest
--   entry; the defining module still transpiles and builds (its own erasure goes
--   `WrapP` → `RecordOps.Point` at pass 4), while a client using `WrapP` in a
--   signature emits `(GHCCore.tyConOpaque "WrapP")` and fails:
--     error: NtUserUnderClient.lean:13:23: Unknown identifier `GHCCore.tyConOpaque`
def eqWrapPInst : Instance :=
  {className := "Eq", headTypes := [.tyCon "WrapP" []],
   dfunName := "$fEqWrapP", dfunUnique := 0}
#guard newtypeInstanceViolations [eqWrapPInst] [] [] == []
-- OBSERVED refusal for the carried case (probe `NtOrphanProbe.hs`, `instance Eq Age`
-- in a module importing `NewtypeBasic (Age, …)`, not committed — Task 7's
-- regression loop keeps exactly one expected-fail fixture):
--   error: newtype instance not representable: `instance Eq Age`
--     `Age` is a newtype (erased → `Int`). …
--   transpile.sh exit 1, no `Generated/NtOrphanProbe.lean` written.

-- LOCAL NEWTYPE OVER AN IMPORTED NEWTYPE (`newtype Wrapped = Wrapped Age`, `Age`
-- imported). The chain crosses the module boundary, and it works only because
-- pass 2 folds the LOCAL substitutions BEFORE `extNts`: `newtypeSubsts` cannot
-- resolve `Age` (no local decl), so it leaves the needle in the underlying
-- string, and the ext entry consumes that needle on a LATER fold step.
def wrappedNtDecl : DataDecl :=
  {name := "Wrapped", kind := "newtype",
   ctors := [ {name := "Wrapped", fields := [ {name := "_", ty := .tyCon "Age" []} ]} ]}
#guard newtypeSubsts [wrappedNtDecl] == [("Wrapped", "(GHCCore.tyConOpaque \"Age\")")]
#guard resolveNewtypes (newtypeSubsts [wrappedNtDecl] ++ [("Age", "Int")])
         "(GHCCore.tyConOpaque \"Wrapped\")" == "Int"
-- The ORDER is load-bearing, not incidental: reversed, the ext entry folds first
-- over a source that does not mention `Age` yet, and the local step then splices
-- a LIVE needle in behind it — pinned as the exact string, so this guard shows
-- the failure rather than merely denying the success.
#guard resolveNewtypes ([("Age", "Int")] ++ newtypeSubsts [wrappedNtDecl])
         "(GHCCore.tyConOpaque \"Wrapped\")" == "(GHCCore.tyConOpaque \"Age\")"
-- Same conclusion at the emitter, which is where the order actually lives: a
-- signature mentioning `Wrapped` erases all the way through to `Int`, with no
-- needle left for pass 4 to turn into a `NewtypeBasic.Age` that does not exist.
def wrappedV : Var :=
  {name := "useWrapped", unique := 4010,
   ty := .tyFun (.tyCon "Wrapped" []) (.tyCon "Wrapped" []), role := .id}
def wrappedX : Var := {name := "x", unique := 4011, ty := .tyCon "Wrapped" [], role := .id}
def wrappedProg : Program :=
  { binds := [.nonRec wrappedV (.lam wrappedX (.var wrappedX))],
    typeDecls := [wrappedNtDecl], instances := [] }
#guard ((emitFullProgram [] wrappedProg [("Age", "Int")]).splitOn
         "(x_4011 : Int) : Int").length == 2
#guard ((emitFullProgram [] wrappedProg [("Age", "Int")]).splitOn "tyConOpaque").length == 1
-- Without the imported half the chain stops mid-way and the needle SURVIVES —
-- loud at `lake build`, never a silently-wrong `Wrapped`-shaped type.
#guard ((emitFullProgram [] wrappedProg []).splitOn
         "(GHCCore.tyConOpaque \"Age\")").length == 3
-- An imported newtype in the underlying is NOT re-exportable (the needle is still
-- there pre-`resolveUserTypes`), so a third module cannot erase `Wrapped` — it
-- gets the surviving needle, loud at `lake build`. Same skip rule as a local
-- user-typed underlying.
#guard newtypeExports [wrappedNtDecl] == []

/-! ## M2 gate fix — local/imported type-name collisions

The hole `parseExtManifest`'s ambiguity check cannot see: it compares manifest
entries against each other, so the module DECLARING the second same-named type is
invisible (its own newtype line is appended only after it emits). Proven
silent-wrong end-to-end on the pre-fix binary — see Emit's "Local-vs-imported
type-name collisions" section for the probe and the four resolution paths. -/

-- The probe's exact shape: local `newtype Tag = Tag [Int]`, imported
-- `Tag⇥newtype⇥Int`.
def tagLocalNtDecl : DataDecl :=
  {name := "Tag", kind := "newtype",
   ctors := [ {name := "Tag",
               fields := [ {name := "_", ty := .tyCon "[]" [.tyCon "Int" []]} ]} ]}
#guard localImportCollisions [tagLocalNtDecl] ["Tag"] == ["Tag"]
-- Local DATA over an imported name is refused identically: there pass 1 consumes
-- the needle into the bare local name before pass 2's erasure can fire, so the
-- imported reference silently becomes the local inductive. Different mechanism,
-- same blindness — hence both kinds are in scope.
def tagLocalDataDecl : DataDecl :=
  {name := "Tag", kind := "data",
   ctors := [ {name := "Tag", fields := [ {name := "t", ty := .tyCon "Int" []} ]} ]}
#guard localImportCollisions [tagLocalDataDecl] ["Tag"] == ["Tag"]
-- Which manifest CHANNEL the imported name came from is not a distinction the
-- caller passes down, and a name in both channels is reported once.
#guard localImportCollisions [tagLocalDataDecl] ["Tag", "Tag"] == ["Tag"]
-- Report order follows the LOCAL decl order (the dump's), and unrelated local
-- decls do not perturb it.
#guard localImportCollisions [tagLocalNtDecl, pointDecl, ageNewtypeDecl]
         ["Age", "Point", "Tag"] == ["Tag", "Point", "Age"]
-- NO OVER-FIRE. A module whose local names are disjoint from the manifest is
-- untouched, and so is every module in a graph with no imported types at all —
-- the check is exactly the identity when either list is empty.
#guard localImportCollisions [tagLocalNtDecl, pointDecl] ["Age", "Rect"] == []
#guard localImportCollisions [] ["Tag", "Age"] == []
#guard localImportCollisions [pointDecl, rectDecl, ageNewtypeDecl] [] == []
-- The self-entry the DATA channel always carries for the module being transpiled
-- (`Point⇥RecordOps` while transpiling `RecordOps`) is NOT a collision — filtered
-- by defining module at the call site, since this function sees names only.
-- Pinned here as the shape that would otherwise refuse every `data`-declaring
-- module: with the filter, `RecordOps`' imported set is empty.
#guard localImportCollisions [pointDecl, rectDecl]
         (([("Point", "RecordOps"), ("Rect", "RecordOps")].filter (·.2 != "RecordOps")).map
           (·.1)) == []
-- …and the same manifest seen from a CLIENT (defining module ≠ this one) does
-- collide, if the client declares its own `Point`.
#guard localImportCollisions [pointDecl]
         (([("Point", "RecordOps")].filter (·.2 != "RecordClient")).map (·.1)) == ["Point"]

-- THE MESSAGE names the type, both origins, the root cause and the remedy. It
-- deliberately states no kind for either side: the dump cannot tell the two
-- references apart whatever they are, and naming one would suggest some pairing
-- is safe.
#guard ((localImportCollisionError "Tag").splitOn "`Tag`").length > 1
#guard ((localImportCollisionError "Tag").splitOn
         "declared locally and imported from the module").length == 2
#guard ((localImportCollisionError "Tag").splitOn
         "records type references unqualified").length == 2
#guard ((localImportCollisionError "Tag").splitOn "rename one of the types").length == 2

-- OBSERVED end-to-end (probe modules `NtSA.hs`/`NtSC.hs`, not committed — the
-- regression loop keeps one expected-fail fixture only).
--   BEFORE: `./transpile.sh examples/haskell/NtSC.hs` → exit 0, EMPTY stderr,
--     `def foreignTag (t_2516 : (List Int)) : (List Int)` for a `NtSA.Tag ->
--     NtSA.Tag` (i.e. `Int -> Int`) function, and `lake build` reported
--     `GhcCoreToLean/Generated/NtSC.lean:16:50: ✅ Valid` for
--     `theorem foreignTag_nil : foreignTag [] = [] := by blaster` — a verdict
--     about the empty list for a function on integers.
--   AFTER: exit 1 before any emission, with
--     error: type name collision: `Tag` is declared locally and imported from
--     the module graph. …
--   The DATA-channel arm was probed the same way (`NtSD.hs`: `import qualified
--   RecordOps` + a local `data Point`) — refused naming `Point`, no
--   `Generated/NtSD.lean` written — while `RecordOps` itself still transpiles
--   with `Point⇥RecordOps` and `Rect⇥RecordOps` in its own manifest, which is
--   what the call site's defining-module filter buys.

/-! ## M3 Task 1 — decl-plugin class-shape dump (`classDecls`)

    Class SHAPES previously never reached the transpiler: the decl-plugin's
    `isUserDataTyCon` filters class TyCons out (`not (isClassTyCon tc)`), and
    class-op Ids and `$p` superclass selectors are not top-level binds, so
    `reconstructClasses` could only ever infer a single-parameter, superclass-free,
    default-free class from its instances. This task adds the `classDecls` channel.
    Emission is UNCHANGED — the observations below are the deliverable, and the
    gate is a byte-identical `Generated/UserClass.lean`.

### The GHC 9.2.7 API actually used

    Verified with `ghci-9.2.7 -package-env=- -package ghc` (NOT from memory —
    `-package-env=-` is needed or the user's global package env fails to resolve).
    The `:i` / `:t` replies, verbatim:

        type ClassOpItem :: *
        type ClassOpItem = (GHC.Types.Var.Id, DefMethInfo)
          	-- Defined in ‘GHC.Core.Class’
        type DefMethInfo :: *
        type DefMethInfo =
          GHC.Maybe.Maybe
            (GHC.Types.Name.Name, DefMethSpec GHC.Core.TyCo.Rep.Type)
          	-- Defined in ‘GHC.Core.Class’
        type DefMethSpec :: * -> *
        data DefMethSpec ty = VanillaDM | GenericDM ty
          	-- Defined in ‘GHC.Types.Basic’
        classOpItems :: Class -> [ClassOpItem]
        classSCTheta :: Class -> [GHC.Core.TyCo.Rep.PredType]
        classTyVars :: Class -> [GHC.Types.Var.TyVar]
        className :: Class -> GHC.Types.Name.Name
        tyConClass_maybe :: TyCon -> GHC.Maybe.Maybe Class
        getClassPredTys_maybe
          :: GHC.Core.TyCo.Rep.PredType
             -> GHC.Maybe.Maybe (Class, [GHC.Core.TyCo.Rep.Type])
        dropForAlls :: Type -> Type
        getTyVar_maybe :: Type -> GHC.Maybe.Maybe TyVar
        splitFunTy_maybe :: Type -> GHC.Maybe.Maybe (Mult, Type, Type)
        isPredTy :: Type -> GHC.Types.Bool

    Two CORRECTIONS to the plan's assumed API:
    * `ClassOpItem`'s second component is NOT `Maybe (Id, DefMethSpec)`. The
      `Maybe` is the whole second component (`DefMethInfo`), and it carries the
      default method's `Name` (`$dm<method>`) plus a `DefMethSpec Type`, not an
      `Id`. `isJust` on it is the `hasDefault` discriminator. M3 Task 4 wants the
      `Name` inside — `fst <$> dmInfo` in `ppClassOp` is the one-line addition.
    * `DefMethSpec`'s constructors are `VanillaDM | GenericDM ty`
      (`GenericDM` = a `DefaultSignatures` generic default). Not used yet.

    A THIRD API fact forced a design choice: `splitTyConApp_maybe` SUCCEEDS on a
    `FunTy` in 9.2 (linear types make it the 5-argument `FUN` application:
    multiplicity, two RuntimeReps, arg, res). The existing `ppType` tries
    `splitTyConApp_maybe` FIRST and has no type-variable case at all, so a method
    type `a -> Int` would render as a `FUN`-headed TyCon with `_Unknown` leaves.
    Hence a SEPARATE `ppMethodTy` (tyvar → arrow → tycon → `_Unknown`), which also
    keeps `typeDecls`/`instances` byte-identical by construction: the task adds a
    channel, it does not re-render the old ones.

### Observation 1 — `UserClass.hs`, the byte-identity fixture

    `.transpile-sandbox/.decls/UserClass.decls.json`, `classDecls` verbatim
    (aeson orders keys alphabetically):

        "classDecls":[{"methods":[{"hasDefault":false,"name":"size","type":
        {"arg":{"name":"a","tag":"TyVar"},"res":{"args":[],"name":"Int",
        "tag":"TyCon"},"tag":"TyFun"}}],"name":"Sized","supers":[],
        "tyVars":["a"]}]

    The method type came out as a real `TyFun (TyVar "a") (TyCon "Int" [])` — i.e.
    the plugin's shape and `reconstructClasses`' head-abstracted guess AGREE
    exactly here, which is why full (whole-record) precedence keeps
    `UserClass.lean` byte-identical rather than merely leaving the channel unused.
    Pinned below, since "identical because the new channel is ignored" and
    "identical because the two sources agree" are indistinguishable from the diff. -/

/-- The `classDecls` entry above, verbatim from the plugin's output file. -/
def m3SizedJson : String :=
  "{\"methods\":[{\"hasDefault\":false,\"name\":\"size\",\"type\":{\"arg\":" ++
  "{\"name\":\"a\",\"tag\":\"TyVar\"},\"res\":{\"args\":[],\"name\":\"Int\"," ++
  "\"tag\":\"TyCon\"},\"tag\":\"TyFun\"}}],\"name\":\"Sized\",\"supers\":[]," ++
  "\"tyVars\":[\"a\"]}"

def m3parseClass (s : String) : Except String ClassDecl := do
  parseClassDecl (← Lean.Json.parse s)

#guard ((m3parseClass m3SizedJson).toOption.map (·.name)) == some "Sized"
#guard ((m3parseClass m3SizedJson).toOption.map (·.tyVars)) == some ["a"]
#guard ((m3parseClass m3SizedJson).toOption.map (·.supers)) == some ([] : List Name)
#guard ((m3parseClass m3SizedJson).toOption.map (·.methods.map (·.name))) == some ["size"]
#guard ((m3parseClass m3SizedJson).toOption.map (·.methods.map (·.hasDefault))) == some [false]
-- THE GATE, in one line: the plugin's own JSON re-emits the class block that
-- `Generated/UserClass.lean` has today, character for character. (M3 Task 4
-- ADAPTATION: `emitClassDecl []` — no defaults for this class, so the gate string
-- is unchanged; `UserClass.lean` was re-verified byte-identical.)
#guard ((m3parseClass m3SizedJson).toOption.map (emitClassDecl []))
         == some "class Sized (a : Type) where\n  size : (a → Int)"

/-! ### Observation 2 — `SuperClass.hs` (new fixture; observation only)

    `class Sized a where size :: a -> Int` / `class Sized a => Container a where
    empty :: a; insert :: Int -> a -> a` / `data Bag = Bag Int` / both instances /
    `sizeViaContainer :: Container a => a -> Int; sizeViaContainer x = size x`.

    `classDecls` (pretty-printed; note `tcg_tcs` order is Container-then-Sized,
    the REVERSE of declaration order — see the ordering note in `mergeClassDecls`):

        [ { "name": "Container", "tyVars": ["a"], "supers": ["Sized"],
            "methods": [ {"name": "empty",  "hasDefault": false,
                          "type": {"tag":"TyVar","name":"a"}},
                         {"name": "insert", "hasDefault": false,
                          "type": {"tag":"TyFun","arg":{"tag":"TyCon","name":"Int","args":[]},
                                   "res":{"tag":"TyFun","arg":{"tag":"TyVar","name":"a"},
                                          "res":{"tag":"TyVar","name":"a"}}}} ] }
        , { "name": "Sized", "tyVars": ["a"], "supers": [],
            "methods": [ {"name": "size", "hasDefault": false,
                          "type": {"tag":"TyFun","arg":{"tag":"TyVar","name":"a"},
                                   "res":{"tag":"TyCon","name":"Int","args":[]}}} ] } ]

    So `supers: ["Sized"]` — the superclass reaches the transpiler for the first
    time. `empty : a` also shows a method whose type is a BARE type variable
    (no arrow), which matters for observation 4.

    HANDOFF for Task 7 (multi-parameter classes): `supers` is a list of NAMES and
    nothing else. `ppSuperPred` keeps the parent class's name and DISCARDS
    `getClassPredTys_maybe`'s second component, the argument types — so
    `class (Sized b) => C a b` dumps as `supers: ["Sized"]` with no record of
    WHICH parameter carries the constraint. That is lossless only under the
    single-parameter assumption this fixture satisfies: with one tyVar there is
    exactly one thing `Sized` can be applied to, which is why the shim comment on
    `ppSuperPred` calls the argument types "recoverable from `classTyVars`" and
    declines to dump them. Multi-parameter classes break that recovery, and
    `["Sized"]` would then be an ambiguity a consumer cannot detect. Task 7 must
    either extend the dump with the argument types or record the limitation and
    refuse — silently picking the first tyVar is the failure mode to avoid.
    PREDICTED, not observed: no fixture declares a multi-parameter class with a
    superclass, so the ambiguous arm is unexercised.

### Observation 3 — the Core spines (`/tmp/transpile-SuperClass.json`)

    Every UNQUALIFIED `$`-name in the whole dump, with counts — 16 distinct, 73
    occurrences. Qualified externals are excluded (`GHC.Types.$tcInt`,
    `GHC.Types.$tcConstraint`, `GHC.Types.$WKindRepVar`, `GHC.Num.$fNumInt`, one
    each): those are other modules' plumbing, not this module's spines.

        39 "$krep"   7 "$trModule"   4 "$fContainerBag"   3 "$fSizedBag"
         2 "$tcSized"  2 "$tcContainer"  2 "$tcBag"
         2 "$dSized"   2 "$dContainer"
         2 "$csize"    2 "$cinsert"     2 "$cempty"
         1 "$tc'C:Sized"   1 "$tc'C:Container"   1 "$tc'Bag"
         1 "$p1Container"

    The three `$tc'…` promoted-datacon reps were missing from this list's first
    pass. Nothing downstream changes — `shouldDrop`'s `$tc` prefix rule eats them
    exactly as it eats `$tcSized` — but the enumeration has to be COMPLETE or the
    negative claims it licenses ((a)'s "no `$cp1Container` anywhere", (c)'s "`$dm`
    — ZERO occurrences") are worth nothing.

    (a) The Container INSTANCE's dfun stores the superclass DICT positionally as
    the dictionary constructor's first field. There is NO selector here, and no
    `$cp1Container`-style bind anywhere in the dump — that spelling does not
    occur at pass-0000:

        ### $fContainerBag#9147 [role=dict]   type: (Container Bag)
          App
            App
              App
                App
                  Var C:Container#9120 [role=id] : _Unknown
                  Type Bag
                Var $fSizedBag#9151 [role=dict] : _Unknown
              Var $cempty#9207 [role=id] : Bag
            Var $cinsert#9212 [role=id] : (Int -> (Bag -> Bag))

    (b) `$p1Container` occurs EXACTLY ONCE, and only because the fixture has a
    superclass USE site (a `Container a`-constrained function calling a `Sized`
    method). Without `sizeViaContainer` the selector appears nowhere and the
    observation would have been a false negative:

        ### sizeViaContainer#8931 [role=id]
        ###   type: (forall a. ((Container _v9077) -> (_v9077 -> Int)))
          Lam (a#9192 [role=tyVar] : Type)
            Lam ($dContainer#9193 [role=dict] : (Container _v9192))
              Let
                $dSized#9195 [role=dict] : (Sized _v9192) =
                  App
                    App
                      Var $p1Container#9117 [role=id] : _Unknown
                      Type _v9192
                    Var $dContainer#9193 [role=dict] : (Container _v9192)
              in
                Lam (x#9078 [role=id] : _v9192)
                  App
                    App
                      App
                        Var size#8930 [role=id] : _Unknown
                        Type _v9192
                      Var $dSized#9195 [role=dict] : (Sized _v9192)
                    Var x#9078 [role=id] : _v9192

    ITS ROLE, precisely: `$p1Container` is a class-op selector Id, so the shim's
    `binderRole` heuristic (`$d`/`$f` prefix ⇒ `dict`) gives it role `id`, NOT
    `dict`. It is nonetheless ERASED before Emit — but by the LET, not by itself:
    the let-BINDER `$dSized` starts with `$d` ⇒ role `dict`, and
    `Lower.lowerExpr`'s `.let_` arm drops a dict-bound `let` whole, RHS included.
    The following `size @a $dSized x` then loses its dict argument the ordinary
    way, and `methodMap` rewrites the bare `size` to `Sized.size`. Net: superclass
    dictionary EXTRACTION already works, for free, today.

    HANDOFF / hedge for Task 5: that erasure is contingent on GHC floating the
    projection to a `$d`-named `let`. If a later pass inlined it into argument
    position (`size @a ($p1Container @a $dContainer) x`), the argument would be an
    `.app`, not a `.var` with role `dict`, so `Lower.isTypeOrDictArg` would return
    false and the selector would survive into Emit. PREDICTED (not observed) as an
    unbound identifier ⇒ loud, not silent-wrong. Re-check if Task 5 changes passes.

    (c) `$dm` — ZERO occurrences. This is a true negative with a known cause:
    `SuperClass.hs` declares no default methods. It is NOT evidence about how GHC
    emits defaults; that observation belongs to Task 4's `DefaultMethods.hs`, and
    deliberately no default was added here to keep the two apart.

### Observation 5 — `hasDefault` is empirically the right discriminator

    Every other dumped field is visible in a committed fixture's output;
    `hasDefault` is not, because no fixture declares a default (deliberately — see
    (c)). So `isJust dmInfo` was verified by throwaway probe `DefProbe.hs`
    (`class Greet a where name :: a -> Int; greet :: a -> Int; greet x = name x + 1`
    + `data G = G Int` + an instance defining only `name`; run, read, deleted — the
    M2 `NtSA.hs`/`NtSC.hs` pattern). The DISCRIMINATING result, within the one
    class:

        class Greet -> [('name', False), ('greet', True)]

    Both-false would have meant `isJust dmInfo` is not the discriminator at
    `typeCheckResultAction` time and the field was a constant-`false`
    silent-wrong; both-true would have meant it keys on something else. Neither
    happened: it separates the defaulted method from the plain one.

### Observation 6 — Task 4 handoffs the probe turned up for free

    From the same throwaway probe. Recorded because they CORRECT the plan's
    fact 5, which assumed an instance relying on a default is dropped whole:

    * `$dmgreet` IS a top-level bind, and its role is `dict` — not because it is
      one, but because the shim's `binderRole` classifies any `$d`-prefixed name
      as a dict. A default-method BODY mislabelled as a dictionary is a trap for
      Task 4's dict-erasure reasoning.
    * GHC ALSO emits a `$cgreet` wrapper for the defaulted method, so
      `emitInstanceUser` does NOT drop the instance — it emitted a complete
      `instance : Greet G where name := … ; greet := _dollar_cgreet_2388`.
    * But `$cgreet` is not top-level-NonRec: it shares a Rec group with the dfun,
      `Rec group: ['$fGreetG', '$cgreet']`. `emitFullProgram`'s `bindHeadName`
      reads only the group's FIRST binder, so the group classifies as `$f…` ⇒
      `isJunkName` ⇒ dropped from BOTH `methodDefs` and `userBinds`. The instance
      then references a def that was never emitted:

        error: …/DefProbe.lean:28:11: Unknown identifier `_dollar_cgreet_2388`

      Loud, but the cause is head-only Rec-group classification, NOT the
      default-method gap — so Task 4 has a second, independent defect to fix, and
      a `$dm`-relying instance is not silently dropped as fact 5 predicted.

### Observation 4 — the expected (loud) degradation, verbatim

    `./transpile.sh examples/haskell/SuperClass.hs` exits 0 with EMPTY stderr and
    emits `class Container (a : Type) where` — no `Sized` parent — and no
    `instance : Container Bag` at all. `lake build GhcCoreToLean.Generated.
    SuperClass` then fails:

        error: …/SuperClass.lean:43:3: failed to synthesize
          Sized t_v9077
        error: …/SuperClass.lean:46:2: failed to synthesize
          Container Bag
        error: …/SuperClass.lean:49:2: failed to synthesize
          Container Bag
        error: …/SuperClass.lean:52:51: translateType: unexpected sort type
          Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))

    Two independent causes, both loud, both Task 5/Task 4 work:
    * `Sized t_v9077` unsynthesized — `supers` is parsed but not emitted, so
      `sizeViaContainer`'s body calls `Sized.size` with only `[Container t]` in
      scope. This is the superclass gap itself (Task 5).
    * `Container Bag` unsynthesized — `emitInstanceUser` DROPPED the Container
      instance whole. Cause: `empty :: a` has no value argument, so
      `firstValArgTy` is `none` for `$cempty : Bag` and `findClassMethod
      "$cempty" "Bag"` cannot match; the all-methods-or-nothing test then fails.
      Task 4 owns replacing that silent whole-instance skip with a per-method
      decision + eprintln, and this is a second, default-independent reason to.
    * the `translateType` error is blaster's, downstream of the two above.

    NOTE the honest limit of "loud" here: the transpiler itself is SILENT (exit 0,
    empty stderr) and the loudness is entirely Lean's. That is the same posture as
    today's other unsupported-class paths, not a new guarantee. -/

-- Parser guards. `hasDefault` is tolerated as ABSENT (⇒ false) so a decls.json
-- from a pre-M3 plugin still parses…
#guard ((m3parseClass
  "{\"name\":\"C\",\"tyVars\":[\"a\"],\"supers\":[],\"methods\":[{\"name\":\"m\",\"type\":{\"tag\":\"TyVar\",\"name\":\"a\"}}]}").toOption.map
    (·.methods.map (·.hasDefault))) == some [false]
-- …but present-and-not-a-boolean is an ERROR, never a silent `false`.
#guard (m3parseClass
  "{\"name\":\"C\",\"tyVars\":[\"a\"],\"supers\":[],\"methods\":[{\"name\":\"m\",\"hasDefault\":\"yes\",\"type\":{\"tag\":\"TyVar\",\"name\":\"a\"}}]}").toOption.isNone
-- The four class-level keys are REQUIRED: a missing one means plugin/transpiler
-- skew, and defaulting it would silently claim "no type parameters" / "no
-- superclasses" — exactly the silent-wrong this channel exists to remove.
#guard (m3parseClass "{\"name\":\"C\",\"tyVars\":[\"a\"],\"methods\":[]}").toOption.isNone
#guard (m3parseClass "{\"name\":\"C\",\"supers\":[],\"methods\":[]}").toOption.isNone
#guard (m3parseClass "{\"tyVars\":[\"a\"],\"supers\":[],\"methods\":[]}").toOption.isNone
#guard (m3parseClass "{\"name\":\"C\",\"tyVars\":[\"a\"],\"supers\":[]}").toOption.isNone
-- `hasDefault` round-trips true when the plugin says so (no fixture produces one
-- yet — Task 4 — so this is the only place the `true` arm is exercised).
#guard ((m3parseClass
  "{\"name\":\"C\",\"tyVars\":[\"a\"],\"supers\":[\"P\"],\"methods\":[{\"name\":\"m\",\"hasDefault\":true,\"type\":{\"tag\":\"TyVar\",\"name\":\"a\"}}]}").toOption.map
    (fun c => (c.supers, c.methods.map (·.hasDefault)))) == some (["P"], [true])

-- `Program.classDecls` is optional in BOTH the ways it can be absent: key
-- missing (legacy JSON, or `ghc-core-shim` run without `--decls`) and key
-- present as `null` (what the shim's `mergeDecls` writes when the plugin
-- produced no such key). Both ⇒ `[]` ⇒ Core reconstruction is the only source.
#guard ((parseProgramFromString "{\"binds\":[]}").toOption.map (·.classDecls.length)) == some 0
#guard ((parseProgramFromString "{\"binds\":[],\"classDecls\":null}").toOption.map
          (·.classDecls.length)) == some 0
#guard ((parseProgramFromString
  ("{\"binds\":[],\"classDecls\":[" ++ m3SizedJson ++ "]}")).toOption.map
    (·.classDecls.map (·.name))) == some ["Sized"]

-- PRECEDENCE. Plugin shapes win whole-record over the reconstruction. Proven
-- e2e too, by feeding the transpiler a hand-perturbed copy of the real
-- `/tmp/transpile-UserClass.json` whose `classDecls` said `tyVars: ["zz"]`: the
-- emitted block became `class Sized (zz : Type) where / size : (zz → Int)`,
-- so the identical-output gate above means the two sources AGREE, not that the
-- new channel is inert.
def m3PluginSized : ClassDecl :=
  { name := "Sized", tyVars := ["zz"], supers := ["P"],
    methods := [ { name := "size", ty := .tyFun (.tyVar "zz") (.tyCon "Int" []), hasDefault := true } ] }
def m3CoreSized : ClassDecl :=
  { name := "Sized", tyVars := ["a"], supers := [],
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
def m3CoreOther : ClassDecl :=
  { name := "Other", tyVars := ["a"], supers := [], methods := [] }
def m3PluginOnly : ClassDecl :=
  { name := "NoInstance", tyVars := ["a"], supers := [], methods := [] }

#guard (mergeClassDecls [m3PluginSized] [m3CoreSized]).map (·.tyVars) == [["zz"]]
#guard (mergeClassDecls [m3PluginSized] [m3CoreSized]).map (·.supers) == [["P"]]
#guard (mergeClassDecls [m3PluginSized] [m3CoreSized]).map (·.methods.map (·.hasDefault))
         == [[true]]
-- Empty plugin channel is the IDENTITY on the reconstruction — the no-sidecar
-- path and every module that declares no class at all.
#guard (mergeClassDecls [] [m3CoreSized, m3CoreOther]).map (·.name) == ["Sized", "Other"]
#guard (mergeClassDecls [] []).length == 0
-- ORDER comes from the reconstruction; a plugin-only class (no local instance, so
-- the reconstruction never saw it) is APPENDED, never interleaved. Deliberate:
-- class decls are emitted unsorted and Lean has no forward references, so
-- reordering before `extends` exists (Task 5) would only churn output.
#guard (mergeClassDecls [m3PluginOnly, m3PluginSized] [m3CoreOther, m3CoreSized]).map (·.name)
         == ["Other", "Sized", "NoInstance"]
-- Builtin class names are filtered out of the PLUGIN channel too. The plugin dumps
-- only the module's own class TyCons so `Eq` cannot normally arrive, but a user
-- class literally named `Eq` has no user-class Lean image (the name is routed to
-- `BEq`/`deriving`) and must not be emitted as one.
#guard (mergeClassDecls [{ name := "Eq", tyVars := ["a"], supers := [], methods := [] }] []).length == 0
#guard (mergeClassDecls [{ name := "Ord", tyVars := ["a"], supers := [], methods := [] }]
          [m3CoreSized]).map (·.name) == ["Sized"]

-- EMISSION is unchanged for the only shape supported end-to-end (single
-- parameter, no superclass) — pinned character-exact at "Dict Task 3" above.
-- `supers` is dropped, silently in the emitter (loudly at the Lean use site):
#guard emitClassDecl []
  { name := "Container", tyVars := ["a"], supers := ["Sized"],
    methods := [ { name := "empty", ty := .tyVar "a" } ] }
    == "class Container (a : Type) where\n  empty : a"
-- A MULTI-parameter class now emits one binder per parameter rather than
-- truncating to the reconstruction's invented single `a`. Pinned as today's
-- behavior, NOT as support: `stripClassConstraints` and `findClassMethod` are
-- still single-head (Task 7), so instances of such a class are still dropped and
-- call sites still fail to synthesize. This is loud either way; the point of
-- pinning it is that Task 7 must change this string deliberately, not by
-- accident.
#guard emitClassDecl []
  { name := "Convert", tyVars := ["a", "b"], supers := [],
    methods := [ { name := "conv", ty := .tyFun (.tyVar "a") (.tyVar "b") } ] }
    == "class Convert (a : Type) (b : Type) where\n  conv : (a → b)"

/-! ### Plugin staleness — how the sandbox actually re-stages (the false-green trap)

    Measured, not assumed. `shim/cabal.project` is `packages: .` ONLY, so
    `cd shim && cabal build` rebuilds the `ghc-core-shim` BINARY and NOT the
    decl-plugin. The plugin is built by the SANDBOX's own generated
    `cabal.project`, which lists `${REPO}/shim/decl-plugin` as a local package, so
    cabal's change detection rebuilds it on the next `./transpile.sh`:
    `.transpile-sandbox/dist-newstyle/.../decl-plugin-0.1.0.0/build/GhcDeclDump.o`
    went from `56688 bytes, Jun 9 08:11` to `95728 bytes, Aug 6 12:52` with no
    manual clean. No force-clean of `decl-plugin-*` was needed or performed.
    (transpile.sh's existing `rm -rf …/transpile-sandbox-*/` is a different
    concern: forcing GHC to RE-RUN the plugins over unchanged staged sources.)

    BOTH layers must be checked separately, because a fresh plugin with a stale
    shim looks exactly like a stale plugin — correct `.decls.json`, no
    `classDecls` in the transpiler's input. Verified at first observation:
    `classDecls` present in `.transpile-sandbox/.decls/UserClass.decls.json` AND
    in `/tmp/transpile-UserClass.json`.

### Regression evidence (post-change)

    * `Generated/UserClass.lean` BYTE-IDENTICAL to the pre-change baseline, in two
      stages: (A) plugin+shim only, nothing consuming the channel; (B) after
      Parse/AST/precedence, with the plugin shape provably driving emission.
      `UserClass.decls.json`'s `module`/`typeDecls`/`instances` also identical.
    * Two identical back-to-back runs produce identical `UserClass.lean`, so the
      byte-identity gate is meaningful (uniques do not drift per run).
    * `NewtypeBasic.lean`, `RecordOps.lean` byte-identical; `NewtypeInstances`
      still REFUSED with a byte-identical error message.
    * Whole top-level corpus (23 fixtures) transpiles `rc=0` except
      `NewtypeInstances` (`rc=1`, by design). SCOPE OF THAT CLAIM: pre-change
      baselines were captured for the four gate fixtures only, so "unchanged" is
      byte-verified for those and argued by construction for the other nineteen —
      `mergeClassDecls [] xs` reduces to `xs` (the `find?` over `[]` returns each
      `cd` unchanged; `xs ++ []`), so a module declaring no class cannot be
      affected, and `UserClass` is the only corpus module that declares one.
    * `lake build GhcCoreToLean.Generated.<M>` green for NewtypeBasic, RecordOps,
      RecordClient, Ratio, Arithmetic, OrdInstance, TupleBasics, ListLibrary.
    * Known red, both PRE-EXISTING or expected: `UserClass` — the fixture's own
      theorem `boxTotal boxes = total boxes + 1` is FALSE and blaster falsifies it
      (it did so in the pre-change baseline run too; the emitted file is
      byte-identical, so nothing about it changed); `SuperClass` — observation 4. -/

/-! ## M3 Task 2 — same-named methods, `emitVar` precedence, `$c/=` scoping

### The branch point, and how reality answered it

    The plan asked: when two classes declare the same method name, do the
    CALL-SITE `Var`s carry distinguishing info (a unique tied to the class-op Id)?
    Fixture-first, and the answer arrived in two parts.

    (1) THE PREMISED PROGRAM DOES NOT EXIST in one module. Class methods are
    module-level names, so a second class declaring `size` is a duplicate
    declaration. `examples/haskell/TwoClassesSameMethod.hs` is that fixture and it
    dies at `cabal build` under the pipeline's GHC 9.2.7 (no error code — those
    start at 9.6), never reaching the transpiler:

        TwoClassesSameMethod.hs:41:9: error:
            Multiple declarations of ‘size’
            Declared at: TwoClassesSameMethod.hs:38:9
                         TwoClassesSameMethod.hs:41:9

    So the "silent first-match by instance-dump order" needs the two classes in
    DIFFERENT modules with this module instantiating both — the path
    `Emit.sameMethodAmbiguities` refuses, and which has no fixture because
    cross-module user classes are not supported end-to-end.

    (2) CALL SITES DO CARRY UNIQUES, but nothing can attribute them to a class.
    From `/tmp/transpile-TwoClassesDistinctMethods.json`, the three `Var`s spelled
    with a method name (name, unique, type, role):

        boxSize      →  ("size",   8931, _Unknown, id)   -- the class-op selector
        crateWeight  →  ("weight", 8929, _Unknown, id)   -- the class-op selector
        applySizer   →  ("size",   8942, TyFun,    id)   -- the local PARAMETER
                        binder: ("size", 8942, TyFun)

    A selector reference is distinguishable, but only from the OTHER `Var`s in the
    dump — mapping unique 8931 to `Sized` would need the class-op Id's unique from
    the decl plugin, which `ppClassOp` does not dump. Adding it is possible: the
    plugin's uniques are `getKey` (tag in the top byte) while the Core dump keeps
    only ghc-dump's number part, and the two reconcile —
    `dfunUnique 8214565720323794489 = 114 * 2^56 + 9785` and 9785 is exactly the
    `$fSizedBox` binder's unique in `/tmp/transpile-UserClass.json`. It was NOT
    done, because the plugin only dumps the module's OWN classes and GHC forbids
    the collision among those: the whole attribution would buy nothing.

    NET: this task's refusal is a TRIPWIRE for an unexercised path, not the removal
    of a live silent-wrong. The live silent-wrong in this same lookup was LOCAL
    BINDER SHADOWING (`MethodRef`), and that is what the uniques are used for.

### Guards -/

-- PRECEDENCE, both directions. `methodMap` is consulted before `valueMap`, which
-- matters only for BARE names now that M1 registered bare operator keys: a
-- qualified `valueMap` key cannot collide with a (always bare) method key.
#guard valueMap "++" == some "List.append"          -- the collision is real…
#guard emitVar [{ method := "++", cls := "Cat" }] []
         {name := "++", unique := 11, ty := .tyCon "_Unknown" [], role := .id} == "Cat._plus__plus_"
#guard emitVar [{ method := "++", cls := "Cat" }] []
         {name := "GHC.Base.++", unique := 12, ty := .tyCon "_Unknown" [], role := .id}
         == "List.append"
-- …and with no user method declaring it, a bare `++` is still the builtin.
#guard emitVar [] [] {name := "++", unique := 13, ty := .tyCon "_Unknown" [], role := .id}
         == "List.append"

-- SHADOWING. Same name, same map — the unique decides. Mirrors the observed
-- `applySizer` shape above (selector 8931 vs parameter 8942).
#guard emitVar [{ method := "size", cls := "Sized", shadowedBy := [8942] }] []
         {name := "size", unique := 8931, ty := .tyCon "_Unknown" [], role := .id}
         == "Sized.size"
#guard emitVar [{ method := "size", cls := "Sized", shadowedBy := [8942] }] []
         {name := "size", unique := 8942, ty := .tyFun (.tyCon "Box" []) (.tyCon "Int" []), role := .id}
         == "size_8942"

-- SHADOWING × BUILTIN NAME — the CROSS of the two tests above, and the cell
-- `size` cannot reach. The three cells above pass under either control flow;
-- this one discriminates. A suppressed match used to be indistinguishable from
-- "no such method" and fall into `valueMap`: harmless for `size` (no image, so
-- the fall-through reached `refId` anyway), the BUILTIN for an operator method.
-- Mirrors the observed `applyEq` shape in `examples/haskell/OperatorShadow.hs`
-- (parameter 9645 vs selector 9721).
#guard valueMap "==" == some "(· == ·)"        -- the fall-through target is live…
#guard emitVar [{ method := "==", cls := "MyEq", shadowedBy := [9645] }] []
         {name := "==", unique := 9645,
          ty := .tyFun (.tyCon "Int" []) (.tyFun (.tyCon "Int" []) (.tyCon "Bool" [])),
          role := .id}
         == "_eq__eq__9645"
-- …and suppression stays scoped to the shadowing unique: the selector in that
-- same module still qualifies.
#guard emitVar [{ method := "==", cls := "MyEq", shadowedBy := [9645] }] []
         {name := "==", unique := 9721, ty := .tyCon "_Unknown" [], role := .id}
         == "MyEq._eq__eq_"

-- `attachMethodShadows` must see EVERY binder kind; a missed one leaves a
-- shadowing occurrence looking like a selector. One synthetic bind carrying all
-- five: top-level binder, lambda, `let` (non-rec), `let rec`, case binder, and
-- alt pattern binder — each spelled `size` with its own unique.
def m3t2ShadowBind : Bind :=
  .nonRec {name := "size", unique := 1, ty := .tyCon "Int" [], role := .id}
    (.lam {name := "size", unique := 2, ty := .tyCon "Int" [], role := .id}
      (.let_ (.nonRec {name := "size", unique := 3, ty := .tyCon "Int" [], role := .id}
                      (.lit (.litInt 0)))
        (.let_ (.rec_ [({name := "size", unique := 4, ty := .tyCon "Int" [], role := .id},
                        .lit (.litInt 0))])
          (.case_ (.lit (.litInt 0))
                  {name := "size", unique := 5, ty := .tyCon "Int" [], role := .id}
                  (.tyCon "Int" [])
                  [.mk (.dataCon "Box") [{name := "size", unique := 6, ty := .tyCon "Int" [], role := .id}]
                       (.lit (.litInt 0))]))))
#guard (attachMethodShadows [m3t2ShadowBind] [{ method := "size", cls := "Sized" }]).map
         (·.shadowedBy) == [[1, 2, 3, 4, 5, 6]]
-- A name no binder uses keeps an empty list (no blanket suppression).
#guard (attachMethodShadows [m3t2ShadowBind] [{ method := "weight", cls := "Weighed" }]).map
         (·.shadowedBy) == [([] : List Unique)]

-- AMBIGUITY REFUSAL. Only exercisable here (see the branch note): two classes
-- declaring `size` — reported once, naming both classes.
def m3t2Sized : ClassDecl :=
  { name := "Sized", tyVars := ["a"], supers := [],
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
def m3t2Weighed : ClassDecl :=
  { name := "Weighed", tyVars := ["a"], supers := [],
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
def m3t2Container : ClassDecl :=
  { name := "Container", tyVars := ["a"], supers := ["Sized"],
    methods := [ { name := "empty", ty := .tyVar "a" },
                 { name := "insert", ty := .tyFun (.tyCon "Int" []) (.tyVar "a") } ] }
#guard sameMethodAmbiguities
         { binds := [], typeDecls := [], instances := [], classDecls := [m3t2Sized, m3t2Weighed] }
         == [("size", ["Sized", "Weighed"])]
-- SuperClass.hs's real shape (distinct method names, one a superclass of the
-- other) must NOT fire, nor must the same class arriving through both channels.
#guard sameMethodAmbiguities
         { binds := [], typeDecls := [], instances := [], classDecls := [m3t2Sized, m3t2Container] }
         == []
#guard sameMethodAmbiguities
         { binds := [csizeBind, dfunBind], typeDecls := [], instances := [sizedInst],
           classDecls := [m3t2Sized] } == []
#guard ((sameMethodAmbiguityError "size" ["Sized", "Weighed"]).splitOn "`Weighed`").length == 2
#guard ((sameMethodAmbiguityError "size" ["Sized", "Weighed"]).splitOn "`Sized`").length == 2

-- `$c/=` SCOPING. Dropped for the head of an `Eq` instance (GHC's derived
-- `not ∘ (==)`, which Lean supplies and whose body would not elaborate); KEPT for
-- a user class's `/=` when no `Eq` instance covers that head.
def m3t2NeqBind : Var :=
  {name := "$c/=", unique := 20,
   ty := .tyFun (.tyCon "Box" []) (.tyFun (.tyCon "Box" []) (.tyCon "Bool" [])), role := .id}
def m3t2EqInstBox : Instance :=
  {className := "Eq", headTypes := [.tyCon "Box" []], dfunName := "$fEqBox", dfunUnique := 21}
def m3t2EqInstCoin : Instance :=
  {className := "Eq", headTypes := [.tyCon "Coin" []], dfunName := "$fEqCoin", dfunUnique := 22}
#guard eqInstanceHeads [m3t2EqInstBox, sizedInst] == ["(GHCCore.tyConOpaque \"Box\")"]
#guard isEqNeqBind [m3t2EqInstBox] m3t2NeqBind == true
#guard isEqNeqBind [m3t2EqInstCoin] m3t2NeqBind == false   -- Eq elsewhere ⇒ keep
#guard isEqNeqBind [] m3t2NeqBind == false                 -- no Eq at all ⇒ keep
-- A user class's `Sized`-style method is never touched by this rule.
#guard isEqNeqBind [m3t2EqInstBox]
         {name := "$csize", unique := 23, ty := .tyFun (.tyCon "Box" []) (.tyCon "Int" []), role := .id}
         == false

-- BUILTIN FALL-THROUGH REFUSAL. A declared method whose name has a `valueMap`
-- image and no map entry would emit the builtin AT A REFERENCE to it;
-- `UserClassNeqWithEq.hs` is the e2e negative. Ordinary method names cannot trip
-- it, and neither can a declaration nobody references.
def m3t2NeqClass : ClassDecl :=
  { name := "Neq", tyVars := ["a"], supers := [],
    methods := [ { name := "/=", ty := .tyFun (.tyVar "a") (.tyFun (.tyVar "a") (.tyCon "Bool" [])) } ] }
/-- A user bind that REFERENCES `/=` (what a call site looks like once the class
    method has no map entry: a bare `Var` the emitter would send to `valueMap`). -/
def m3t2NeqUse : Bind :=
  .nonRec {name := "differs", unique := 30,
           ty := .tyFun (.tyCon "Box" []) (.tyCon "Bool" []), role := .id}
          (.app (.var {name := "/=", unique := 31, ty := .tyCon "_Unknown" [], role := .id})
                (.var {name := "b", unique := 32, ty := .tyCon "Box" [], role := .id}))
#guard unmappedOperatorMethods
         { binds := [m3t2NeqUse], typeDecls := [], instances := [], classDecls := [m3t2NeqClass] }
         == [("Neq", "/=")]
-- USE-LEVEL, and this is the measured half: declared, never referenced ⇒ NOT
-- refused. A probe of exactly this shape (`class Neq a where (/=)`, no instance,
-- no use) transpiled AND `lake build`-ed clean before the guard existed, so
-- refusing it would remove a working module for no soundness gain. Add a
-- reference (`allDiffer x y = x /= y`, still no instance) and the pre-guard
-- pipeline emitted the builtin at a type variable and failed
-- `failed to synthesize` — that case is the one refused, earlier.
#guard unmappedOperatorMethods
         { binds := [], typeDecls := [], instances := [], classDecls := [m3t2NeqClass] }
         == []
#guard unmappedOperatorMethods
         { binds := [m3t2NeqUse], typeDecls := [], instances := [],
           classDecls := [m3t2Sized, m3t2Container] }
         == []
-- With the `$c/=` bind present (an instance whose dfun names it), the map has the
-- entry and nothing is refused — the `UserClassNeq.hs` case.
def m3t2NeqCBind : Bind :=
  .nonRec m3t2NeqBind (.lam {name := "b", unique := 24, ty := .tyCon "Box" [], role := .id}
                            (.var {name := "GHC.Types.True", unique := 25,
                                   ty := .tyCon "_Unknown" [], role := .id}))
def m3t2NeqDfun : Bind :=
  .nonRec {name := "$fNeqBox", unique := 26, ty := .tyCon "Neq" [.tyCon "Box" []], role := .id}
          (.var m3t2NeqBind)
def m3t2NeqInst : Instance :=
  {className := "Neq", headTypes := [.tyCon "Box" []], dfunName := "$fNeqBox", dfunUnique := 26}
#guard (reconstructClasses [m3t2NeqCBind, m3t2NeqDfun] [m3t2NeqInst]).2
         == [{ method := "/=", cls := "Neq" }]
#guard unmappedOperatorMethods
         { binds := [m3t2NeqCBind, m3t2NeqDfun], typeDecls := [], instances := [m3t2NeqInst],
           classDecls := [m3t2NeqClass] } == []

/-! ### e2e evidence (fixtures)

    `TwoClassesDistinctMethods.hs` — two classes, distinct method names, instances
    on different data types, both call sites plus the shadowing case. BEFORE the
    fix the shadowed parameter was overwritten by the class method:

        def applySizer (size_8942 : (Box → Int)) : Int :=
          (Sized.size) ((Box.Box) ((3 : Int)))

    Lean accepted it with only `unused variable size_8942`, and blaster FALSIFIED
    `∀ k, applySizer (fun _ => k) = k` with `k: 4` (the body is constantly 3).
    AFTER: `(size_8942) ((Box.Box) ((3 : Int)))`, and all three properties
    (`boxSize_correct`, `crateWeight_correct`, `applySizer_uses_its_argument`) are
    `✅ Valid`. The two class call sites still emit `Sized.size` / `Weighed.weight`,
    each its own class's.

    `UserClassNeq.hs` — a user class declaring `(/=)`. BEFORE, `Main.lean`'s
    unconditional `$c/=` drop removed its only method, `emitInstanceUser` dropped
    the whole instance, and `lake build` failed `failed to synthesize` at line 20
    (plus a `translateType: unexpected sort type` from blaster on the orphaned
    property). AFTER: the `$c/=` def, `instance : Neq Box where _slash__eq_ := …`,
    a call site rewritten to `Neq._slash__eq_`, and `differs_is_inequality`
    `✅ Valid`.

    `UserClassNeqWithEq.hs` — the same class at a head that ALSO has `deriving Eq`.
    Both `$c/=` binds share the head type, so both are dropped and the map has no
    entry; BEFORE this task's second refusal the call site silently became the
    builtin (`(fun a b => !(a == b))`, accepted because `deriving Eq` supplied
    `BEq Box`). NOW refused, `rc=1`, no file written.

### Regression evidence (post-change)

    Byte-identical to a baseline built from the pre-change sources (`git stash` of
    Emit/Main/Unit, rebuilt binary, transpiled, diffed): `UserClass`, `Ratio`,
    `Arithmetic`, `OrdInstance`, `NewtypeBasic`, `RecordOps`, `SuperClass`.
    `Ratio`/`Arithmetic`/`OrdInstance` are the ones that carry `$c/=` binds
    (`Ratio` has TWO Eq instances — `$c/=` at uniques 12069 and 12087 — so it also
    pins that the head-keyed rule drops both), which is what makes the `$c/=`
    change verified rather than argued. `NewtypeInstances` still refused with a
    byte-identical message.

    `lake build GhcCoreToLean.Generated.<M>` green (0 errors) for NewtypeBasic,
    RecordOps, Ratio, Arithmetic, OrdInstance, UserClassNeq,
    TwoClassesDistinctMethods.

    NOT re-verified this task: the remaining ~15 corpus fixtures declare no class
    at all, so `reconstructClasses` returns `([], [])`, `attachMethodShadows`
    returns `[]`, and both new guards return `[]` — the only reachable change for
    them is the `$c/=` rule, byte-verified on the three fixtures that have one. -/

/-! ## M3 Task 3 — builtin class constraints in signatures (`Maps.classConMap`)

### The two defects, as observed before the change

    `examples/haskell/BuiltinConstraints.hs` transpiled with the pre-change binary
    (`/tmp/BuiltinConstraints-before.lean`). `stripClassConstraints`' gate was
    `classNames` = USER classes only, so a builtin constraint arrow was never
    peeled and BOTH callers of that function went wrong at once:

        def allSame {t_v3009 : Type} (x_3010 : ((GHCCore.tyConOpaque "Eq") (t_v3009)))
                    (y_3011 : t_v3009) : (t_v3009 → Bool) :=
          (((· == ·)) (x_3010)) (y_3011)

    (a) the first VALUE binder is typed as the dictionary — `Lower` had already
    erased the dict at the value level, so `x_3010` IS the Haskell `x`; (b) the
    result type is `(t_v3009 → Bool)` instead of `Bool`, because `resTyOf` peeled
    two arrows off a type that still had three. Loud in both cases (there is no
    `GHCCore.tyConOpaque` in scope in a Generated module at all), never
    silent-wrong — but nothing with a builtin constraint could compile.

    The widening therefore lives INSIDE `stripClassConstraintsGo`, not in a gate
    threaded to each caller, so `emitDefHeader` and `resTyOf` cannot drift apart
    again.

### Which binder set — probed, not assumed

    Haskell's `Ord` methods do not map to `[Ord t]`. The transpiler's images are
    `decide (a < b)` / `decide (a ≤ b)` (Lean's `<`/`≤` are `Prop`-valued),
    `Min.min`/`Max.max`, and `compare`. Measured in a scratch file against
    `fun (x y : t) => …` for each image:

        [Ord t]                                    → FAILS: "failed to synthesize
                                                     LT t" / "LE t" / "Min t"
                                                     (`compare` alone is fine)
        + [LT t] [LE t] [Min t] [Max t] [BEq t]    → FAILS: "failed to synthesize
                                                     Decidable (a < b)" / "(a ≤ b)"
        + [DecidableLT t] [DecidableLE t]          → ALL elaborate: `<`, `≤`, `>`,
                                                     `≥`, `Min.min`, `Max.max`,
                                                     `compare`, `==`,
                                                     `(List.max? xs).getD default`,
                                                     `(List.min? xs).getD default`,
                                                     `xs.contains x`
        drop [Ord t] from that set                 → FAILS: `compare` needs it

    Lean core makes `ltOfOrd`/`leOfOrd`/`minOfLe`/`maxOfLe` plain DEFS, not
    instances, which is why the caller has to supply them. Callers can: `Int`
    satisfies the whole set, and so does a `deriving Ord` inductive carrying
    `emitDataDecl`'s companion instances (`instance : LT T := ltOfOrd`, …) —
    checked by elaborating a call at both.

    `[BEq t]` belongs in the Ord set because Haskell's `Ord a` implies `Eq a`
    (GHC projects it with `$p1Ord`), so an `Ord`-constrained body may use `==`.
    `ordEq` in the fixture is exactly that body and would not elaborate without it.

    REJECTED ALTERNATIVE (measured, not assumed): keep the header at `[Ord t]`
    alone and derive LT/LE/Min/Max in the BODY, which would make the order
    COHERENT by construction rather than trusting the caller to pass an `LT` that
    agrees with its `Ord`. `have _i : LT t := ltOfOrd` does NOT work — the fvar is
    opaque, so `Decidable (a < b)` is not found and core's
    `DecidableRel (@LT.lt α ltOfOrd)` instance cannot match (`Decidable
    (@LT.lt t ltOfOrd a b)` vs `Decidable (@LT.lt t _i a b)`). Zeta-transparent
    `let _i : LT t := ltOfOrd` DOES work for `<`, but `Min`/`Max` then need their
    own `let`-bound `DecidableRel LE.le` companion, and the whole scheme rewrites
    every constrained def's BODY on an elaboration-transparency detail. Out of
    scope here.
    SCOPE OF THE GENERALITY CAVEAT this leaves — the property is FAITHFULNESS,
    NOT coherence. The emitted Lean def is MORE general than its Haskell source,
    since nothing ties the `LT`/`LE`/`Min`/`Max`/`BEq` arguments to the `Ord` one.
    The two halves of that set have DIFFERENT statuses and must not be lumped:

    * `LT`/`LE`/`Min`/`Max` are coherent BY CONSTRUCTION at every type the
      transpiler emits, because there is only ever one `Ord` for them to come
      from: `emitDataDecl` emits the companions as `leOfOrd`/`ltOfOrd`/`minOfLe`/
      `maxOfLe` off that type's single `Ord` (its `ordInsts` block), and `Int`'s
      core instances agree the same way.
    * `[BEq t]` is DELIBERATELY left untied, and it is NOT coherent by
      construction — because in Haskell it is not either. `Eq a` and `Ord a` are
      INDEPENDENT dictionaries; `Ord`'s superclass edge (`$p1Ord`) demands that an
      `Eq` exist, not that it agree with `compare`. So
      `data Rat = Rat Int Int deriving Ord` plus a hand-written cross-multiply
      `instance Eq Rat` is legal Haskell that this transpiler emits WITHOUT
      refusal, and at that type `==` (cross-multiply) and `<`/`compare`
      (structural) genuinely diverge — in the emitted Lean exactly as in GHC.
      Divergence there is the FAITHFUL answer, not a defect. It is therefore
      FALSE that every instantiation the transpiler can produce is coherent; what
      is true is that every binder is the image of a DISTINCT field of the Haskell
      dictionary its constraint stands for, so each one is faithful to something.

    Witnessed, not asserted: the `M3T3R` guards in the INSTANCE SELECTION
    subsection at the end of this block ARE that `Rat` shape (derived `Ord` + the
    four companions + a hand-written cross-multiply `BEq`) and pin `==` to
    cross-multiply while the order stays structural.

    HAZARD, named so that no future maintainer "simplifies" it away: the tempting
    cleanup is to drop `[BEq t]` from the `Ord` set and obtain `==` from `Ord`
    instead (`compare a b == .eq`, or a `BEq` synthesised from the `Ord`
    argument). Doing that is SILENT-WRONG at exactly the `Rat` shape above —
    every `Ord`-constrained function applied at `Rat` would begin reporting
    STRUCTURAL equality where Haskell reports the hand-written cross-multiply
    result, with no error raised anywhere. The `M3T3R` `#guard`s break if it is
    ever done, which is why they are guards rather than prose. What remains
    outside the image of any Haskell program is only the other direction: a
    HAND-WRITTEN Lean call passing an `LT` that disagrees with its `Ord`.

    TASK 6 MUST DECIDE AND PIN THE CONVERSE, which this task's scope does not
    reach. Today `emitDataDecl` is the only source of the `LT`/`LE`/`Min`/`Max`
    companions and derives all four FROM `compare`. Task 6 stops replacing a
    hand-written Haskell `Ord` with `deriving Ord` and emits
    `instance : Ord T where compare := <$ccompare ref>` — but per the plan's Task 6
    bullet it reuses those same companions, so `<`/`≤`/`min`/`max` at `T` stay
    FUNCTIONS OF `compare` and a hand-written `$c<` or `$cmin` body that disagrees
    with the type's own `$ccompare` is silently discarded. That is divergence in
    the OPPOSITE direction from the hazard above — Lean would be MORE lawful than
    a law-violating Haskell instance, which is not automatically the wrong call,
    but it IS a call, and Task 6 owns making it explicit and pinning it. (Plan:
    `docs/superpowers/plans/2026-08-06-m3-typeclass-completeness.md`, Task 6.
    Distinct from the forward-reference at the end of this block, which is about
    instance SELECTION going live rather than companion derivation discarding
    method bodies.)

### Why `Num` is four binders and no `OfNat` — measured

    `emitLiteral` emits numeric literals Int-ASCRIBED (`(1 : Int)`), so
    `[OfNat t 0] [OfNat t 1]` would be dead weight. Probed on a throwaway
    `incr :: Num a => a -> a; incr x = x + 1`, which emits
    `(((· + ·)) (x_2273)) ((id) ((1 : Int)))` (Haskell's `fromInteger` maps to
    `id`) and fails with

        error: failed to synthesize  HAdd t_v2272 Int t_v2272

    — an `OfNat` binder would not have helped; the ascription is the blocker. And
    `absG x = abs x` emits `(fun a => if a < 0 then -a else a)`, failing
    "failed to synthesize OfNat t_v2132 0" AND "LT t_v2132": `abs`/`signum` need
    the Ord binder set a `Num a` constraint does not supply. All LOUD, no
    silent-wrong, so `Num` is mapped for the `+`/`-`/`*`/`negate` fragment and the
    literal / `abs` / `signum` fragment is a recorded deferral.

### Unmapped builtin stays LOUD

    Probed on a throwaway `halve :: Fractional a => a -> a`. The constraint head
    arrives in the same shape as the mapped ones
    (`{"args":[{"name":"_v2131","tag":"TyVar"}],"name":"Fractional","tag":"TyCon"}`),
    `classConMap` returns `none`, the peel stops, and the emitted def carries the
    pre-change defect shape on purpose — two hard errors, `Unknown identifier
    'GHCCore.tyConOpaque'` and `Unknown identifier 'GHC.Real._slash_'`. -/

#guard classConMap "Eq" == some ["[BEq {t}]"]
-- ORDER IS LOAD-BEARING, so the whole SEQUENCE is pinned, not membership:
-- `DecidableLT t` = `DecidableRel (LT.lt : t → t → Prop)` only elaborates with
-- `LT t` already bound (same for `DecidableLE`/`LE`).
#guard classConMap "Ord" ==
  some ["[Ord {t}]", "[LT {t}]", "[LE {t}]", "[DecidableLT {t}]", "[DecidableLE {t}]",
        "[Min {t}]", "[Max {t}]", "[BEq {t}]"]
#guard classConMap "Num" == some ["[Add {t}]", "[Sub {t}]", "[Mul {t}]", "[Neg {t}]"]
-- Qualified hedges (the shim delivers BARE heads; observed above).
#guard classConMap "GHC.Classes.Eq" == classConMap "Eq"
#guard classConMap "GHC.Classes.Ord" == classConMap "Ord"
#guard classConMap "GHC.Num.Num" == classConMap "Num"
-- Deliberately unmapped builtins — `none` here is what keeps them loud.
#guard classConMap "Fractional" == none
#guard classConMap "Integral"   == none
#guard classConMap "Real"       == none
#guard classConMap "Show"       == none
#guard classConMap "Enum"       == none
#guard classConMap "Sized"      == none   -- a USER class is not this map's business

/-! ### `stripClassConstraints` — binders AND the stripped type

    The types below are the shapes actually dumped for
    `examples/haskell/BuiltinConstraints.hs` (`/tmp/transpile-BuiltinConstraints.json`):
    `ForAll a. TyFun (TyCon "Eq" [TyVar "_v3009"]) …`, class head BARE. -/

def m3t3TyA : GHCType := .tyVar "_v3009"

-- allSame :: Eq a => a -> a -> Bool
def m3t3AllSameVar : Var :=
  { name := "allSame", unique := 2129, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Eq" [m3t3TyA])
            (.tyFun m3t3TyA (.tyFun m3t3TyA (.tyCon "Bool" [])))) }
#guard (stripClassConstraints [] m3t3AllSameVar.ty).1 == ["[BEq t_v3009]"]
-- The stripped type is the VALUE signature — one arrow shorter than what
-- `resTyOf` used to see, which is defect (b).
#guard emitType (stripClassConstraints [] m3t3AllSameVar.ty).2
         == "(t_v3009 → (t_v3009 → Bool))"

-- maxG :: Ord a => [a] -> a
def m3t3TyB : GHCType := .tyVar "_v3007"
def m3t3MaxGVar : Var :=
  { name := "maxG", unique := 2130, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Ord" [m3t3TyB])
            (.tyFun (.tyCon "[]" [m3t3TyB]) m3t3TyB)) }
#guard (stripClassConstraints [] m3t3MaxGVar.ty).1
         == ["[Ord t_v3007]", "[LT t_v3007]", "[LE t_v3007]", "[DecidableLT t_v3007]",
             "[DecidableLE t_v3007]", "[Min t_v3007]", "[Max t_v3007]", "[BEq t_v3007]"]
#guard emitType (stripClassConstraints [] m3t3MaxGVar.ty).2 == "(List t_v3007 → t_v3007)"

-- USER classes are matched FIRST and emit exactly as before: `[C t]`.
def m3t3TyD : GHCType := .tyVar "_v9"
def m3t3TotalVar : Var :=
  { name := "total", unique := 9, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Sized" [m3t3TyD])
            (.tyFun (.tyCon "[]" [m3t3TyD]) (.tyCon "Int" []))) }
#guard (stripClassConstraints ["Sized"] m3t3TotalVar.ty).1 == ["[Sized t_v9]"]
#guard emitType (stripClassConstraints ["Sized"] m3t3TotalVar.ty).2 == "(List t_v9 → Int)"

-- An UNMAPPED builtin peels NOTHING and hands back the type UNCHANGED (the
-- `tyConOpaque` head is what then fails loud in Lean).
def m3t3TyC : GHCType := .tyVar "_v2131"
def m3t3HalveVar : Var :=
  { name := "halve", unique := 2131, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Fractional" [m3t3TyC]) (.tyFun m3t3TyC m3t3TyC)) }
#guard (stripClassConstraints [] m3t3HalveVar.ty).1 == []
#guard emitType (stripClassConstraints [] m3t3HalveVar.ty).2
         == "(((GHCCore.tyConOpaque \"Fractional\") (t_v2131)) → (t_v2131 → t_v2131))"

-- A non-tyvar constraint head (`Eq [a]`) does not match the peel pattern either —
-- UNCHANGED from before this map existed, and stated so it reads as scoped rather
-- than missed. Unreachable from the corpus (GHC passes no dictionary for a
-- monomorphic signature).
def m3t3ListEqVar : Var :=
  { name := "listEq", unique := 11, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Eq" [.tyCon "[]" [m3t3TyA]])
            (.tyFun (.tyCon "[]" [m3t3TyA]) (.tyCon "Bool" []))) }
#guard (stripClassConstraints [] m3t3ListEqVar.ty).1 == []
#guard emitType (stripClassConstraints [] m3t3ListEqVar.ty).2
         == "(((GHCCore.tyConOpaque \"Eq\") (List t_v3009)) → (List t_v3009 → Bool))"

-- `(Eq a, Ord a) =>` peels two constraints whose images OVERLAP (`[BEq t]` is in
-- the Ord set). The wrapper dedups; first-occurrence order survives, so `LT`
-- still precedes `DecidableLT`.
def m3t3BothVar : Var :=
  { name := "both", unique := 10, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Eq" [m3t3TyA])
            (.tyFun (.tyCon "Ord" [m3t3TyA]) (.tyFun m3t3TyA (.tyCon "Bool" [])))) }
#guard (stripClassConstraintsGo [] [] m3t3BothVar.ty).1.length == 9   -- pre-dedup
#guard (stripClassConstraints [] m3t3BothVar.ty).1
         == ["[BEq t_v3009]", "[Ord t_v3009]", "[LT t_v3009]", "[LE t_v3009]",
             "[DecidableLT t_v3009]", "[DecidableLE t_v3009]", "[Min t_v3009]",
             "[Max t_v3009]"]
-- The OTHER source order, pinned too: `(Ord a, Eq a) =>` yields the canonical
-- EIGHT with `[BEq t]` kept exactly once, in its Ord-set position (8th) — because
-- `dedup` keeps FIRST occurrences, so here it is the TRAILING `Eq`'s image that is
-- dropped, not the leading one. Both orders are guarded because the SEQUENCE is
-- load-bearing (`DecidableLT` only elaborates with `LT` already bound): pinning
-- one source order would leave the other free to drift.
def m3t3BothRevVar : Var :=
  { name := "bothRev", unique := 13, role := .id,
    ty := .forAll "a" (.tyFun (.tyCon "Ord" [m3t3TyA])
            (.tyFun (.tyCon "Eq" [m3t3TyA]) (.tyFun m3t3TyA (.tyCon "Bool" [])))) }
#guard (stripClassConstraintsGo [] [] m3t3BothRevVar.ty).1.length == 9   -- pre-dedup
#guard (stripClassConstraints [] m3t3BothRevVar.ty).1
         == ["[Ord t_v3009]", "[LT t_v3009]", "[LE t_v3009]", "[DecidableLT t_v3009]",
             "[DecidableLE t_v3009]", "[Min t_v3009]", "[Max t_v3009]", "[BEq t_v3009]"]
-- …i.e. `classConMap "Ord"`'s own sequence instantiated, with nothing added and
-- nothing reordered by the extra `Eq`.
#guard (stripClassConstraints [] m3t3BothRevVar.ty).1
         == ((classConMap "Ord").getD []).map (·.replace "{t}" "t_v3009")

-- Different type variables are different binders and are never merged.
def m3t3TwoVarVar : Var :=
  { name := "twoVar", unique := 12, role := .id,
    ty := .forAll "a" (.forAll "b" (.tyFun (.tyCon "Eq" [m3t3TyA])
            (.tyFun (.tyCon "Eq" [.tyVar "_v3010"]) (.tyCon "Bool" [])))) }
#guard (stripClassConstraints [] m3t3TwoVarVar.ty).1 == ["[BEq t_v3009]", "[BEq t_v3010]"]

/-! ### `resTyOf` alignment — the whole header, character-exact

    These pin defect (b) shut: the strings below are BYTE-IDENTICAL to the
    corresponding defs in `GhcCoreToLean/Generated/BuiltinConstraints.lean`, so a
    regression in either `emitDefHeader`'s binder list or `emitBind`'s `resTyOf`
    breaks the build here rather than only at a fixture. -/

def m3t3XV : Var := { name := "x", unique := 3010, ty := m3t3TyA, role := .id }
def m3t3YV : Var := { name := "y", unique := 3011, ty := m3t3TyA, role := .id }
def m3t3EqV : Var :=
  { name := "GHC.Classes.==", unique := 0, ty := .tyCon "_Unknown" [], role := .id }
-- The rhs has TWO lambdas, not four: `Lower` already erased the type binder and
-- the `$dEq` dict binder (role `dict`) — that erasure is what makes the type-side
-- peel necessary. Observed in /tmp/transpile-BuiltinConstraints.json.
def m3t3AllSameBind : Bind :=
  .nonRec m3t3AllSameVar
    (.lam m3t3XV (.lam m3t3YV (.app (.app (.var m3t3EqV) (.var m3t3XV)) (.var m3t3YV))))
#guard emitBind [] [] [] m3t3AllSameBind ==
  "def allSame {t_v3009 : Type} [BEq t_v3009] (x_3010 : t_v3009) (y_3011 : t_v3009) : Bool :=\n" ++
  "  (((· == ·)) (x_3010)) (y_3011)"

-- `Ord a => [a] -> a` with a PARTIAL body: M1's `[Inhabited t]` (for the ⊥ →
-- `default` image of `maximum`) and the Ord binder set have to coexist, implicits
-- first. This is the header the plan predicted and the first e2e exercise of the
-- polymorphic partial path.
def m3t3XsV : Var := { name := "xs", unique := 3014, ty := .tyCon "[]" [m3t3TyB], role := .id }
def m3t3MaxV : Var :=
  { name := "Data.Foldable.maximum", unique := 0, ty := .tyCon "_Unknown" [], role := .id }
def m3t3MaxGBind : Bind :=
  .nonRec m3t3MaxGVar (.lam m3t3XsV (.app (.var m3t3MaxV) (.var m3t3XsV)))
#guard emitBind [] [] [] m3t3MaxGBind ==
  "def maxG {t_v3007 : Type} [Inhabited t_v3007] [Ord t_v3007] [LT t_v3007] [LE t_v3007] " ++
  "[DecidableLT t_v3007] [DecidableLE t_v3007] [Min t_v3007] [Max t_v3007] [BEq t_v3007] " ++
  "(xs_3014 : List t_v3007) : t_v3007 :=\n" ++
  "  ((fun xs => (List.max? xs).getD default)) (xs_3014)"

-- The LOUD shape, pinned so "unmapped builtin stays loud" is a test and not a
-- hope: the dict-typed first binder AND the shifted result type are BOTH still
-- there for `Fractional`. This is character-identical to the pre-change output
-- for `Eq` with the class name swapped — i.e. it is defect (a)+(b) preserved
-- deliberately, exactly where a mapping is missing.
def m3t3HXV : Var := { name := "x", unique := 2435, ty := m3t3TyC, role := .id }
def m3t3DivV : Var :=
  { name := "GHC.Real./", unique := 0, ty := .tyCon "_Unknown" [], role := .id }
def m3t3HalveBind : Bind :=
  .nonRec m3t3HalveVar
    (.lam m3t3HXV (.app (.app (.var m3t3DivV) (.var m3t3HXV)) (.var m3t3HXV)))
#guard emitBind [] [] [] m3t3HalveBind ==
  "def halve {t_v2131 : Type} (x_2435 : ((GHCCore.tyConOpaque \"Fractional\") (t_v2131))) : " ++
  "(t_v2131 → t_v2131) :=\n" ++
  "  ((GHC.Real._slash_) (x_2435)) (x_2435)"

/-! ### The `[BEq t]` binder makes INSTANCE SELECTION load-bearing — pinned

    New risk this task introduces: `[BEq t]` in the `Eq` and `Ord` sets means a
    call site now RESOLVES a `BEq` instance where nothing resolved one before. A
    type with a HAND-WRITTEN Eq (emitted as `instance : BEq T`) that ALSO has Ord
    gets a SECOND candidate, because `emitDataDecl` derives `DecidableEq` whenever
    `hasOrd` and core's `instBEqOfDecidableEq` lifts that to `BEq T`. If the
    derived structural one won, an `Eq`-constrained function applied at that type
    would return structural equality where Haskell returns the hand-written
    result — silent-wrong.

    It does not win. Measured below in the emitter's own section order (data +
    `deriving` first, instances after — fact 7's ordering constraint): the
    locally-declared `instance : BEq R` beats core's generic lift, `#synth BEq R`
    answers `instBEqR`, and the cross-multiply semantics survives both a direct
    `==` and a `[BEq t]`-constrained polymorphic call. Pinned as a `#guard` rather
    than a comment precisely because the failing direction would be silent.

    NOT EXERCISED e2e: no corpus type has both a hand-written Eq and an Ord —
    `Ratio`'s `CustomRatio`/`CustomRatioSOP` have hand-written Eq and NO Ord (so
    no `DecidableEq` is derived for them at all), and `OrdInstance`'s `Coin`
    derives BOTH (one route only). So this is a scoped guard on the mechanism, not
    fixture evidence. It becomes live in Task 6, which stops replacing
    hand-written Ord with `deriving Ord`. -/

inductive M3T3R where
  | mk : Int → Int → M3T3R
deriving Repr, Inhabited, DecidableEq, Ord

instance : LE M3T3R := leOfOrd
instance : LT M3T3R := ltOfOrd
instance : Min M3T3R := minOfLe
instance : Max M3T3R := maxOfLe
-- The hand-written cross-multiply Eq, in the shape `emitInstance` produces.
instance : BEq M3T3R where
  beq a b := match a, b with | .mk p q, .mk r s => p * s == r * q

-- `allSame`'s emitted shape, at the binder set this task assigns to `Eq a =>`.
def m3t3AllSameAt {t : Type} [BEq t] (x y : t) : Bool := (((· == ·)) x) y

-- Haskell semantics (hand-written): 1/2 == 2/4 is TRUE. Structural: FALSE.
#guard m3t3AllSameAt (M3T3R.mk 1 2) (M3T3R.mk 2 4) == true
#guard ((M3T3R.mk 1 2) == (M3T3R.mk 2 4)) == true
-- …and the hand-written instance is still discriminating, not constantly true.
#guard m3t3AllSameAt (M3T3R.mk 1 2) (M3T3R.mk 3 4) == false

/-! ### e2e evidence (`examples/haskell/BuiltinConstraints.hs`)

    `lake build GhcCoreToLean.Generated.BuiltinConstraints` — 0 errors, all nine
    quantified properties `✅ Valid` under blaster at the `Int` instantiation of
    the POLYMORPHIC defs (no monomorphic wrapper needed): `allSame_isBEq`,
    `notSame_isNotBEq`, `allSameInt_agrees`, `ordered_isLt`, `ordEq_isLe`,
    `maxG_pair`, `double_isAdd`, `sumSquares_expand`, `negateBoth_expand`; plus
    four ground `decide` properties (`maxG_example`, `maxG_empty_isDefault`,
    `clamp_middle`, `clamp_above`). `ordEq_isLe` and `maxG_pair` are the two that
    exercise real order theory (`(x<y) ∨ (x==y) = (x≤y)`, and `List.max?` over a
    two-element list) — both went through as-is, so no `decide` fallback was
    needed anywhere.

    The polymorphic defs COMPILING is itself the feature: before the change none
    of them could, and the `maxG` header is the first one carrying an M1
    `[Inhabited t]` binder alongside a builtin constraint set.

### Regression evidence (post-change)

    Corpus-wide `grep -n '::.*=>' examples/haskell/*.hs` shows the ONLY builtin
    constraints anywhere are `BuiltinConstraints.hs`'s own; every other
    constrained signature is a USER class (`UserClass.hs`'s `Sized a =>`,
    `SuperClass.hs`'s `Container a =>`), which takes the unchanged
    `classNames`-first branch — so byte-identity is expected everywhere else, and
    it was MEASURED rather than argued: baselines were built by `git stash`ing
    Maps/Emit/Unit, rebuilding the binary, transpiling, restoring, and diffing.

    BYTE-IDENTICAL (12/12): `UserClass`, `Ratio`, `RecordOps`, `NewtypeBasic`,
    `SuperClass` (still unchanged-degraded — the Task 5 `extends` gap, untouched
    here), `OrdInstance`, `Arithmetic`, `ListLibrary`, `TupleBasics`,
    `PreludeNames`, `NumOrd`, `PartialHead`. The last two are the ones that would
    have moved had the peel over-fired: `NumOrd`/`PartialHead` use the very
    `Ord`/`Num`/partial operators this task maps, but MONOMORPHICALLY (no
    dictionary is passed, so there is no constraint arrow to peel).

    Refusals intact: `NewtypeInstances` (message identical modulo the output path
    passed on the command line, no file written) and `UserClassNeqWithEq`
    (`rc=1`, Task 2's builtin-method-collision refusal).

    `lake build GhcCoreToLean.Generated.<M>` green (0 errors): BuiltinConstraints,
    Ratio, Arithmetic, OrdInstance, NewtypeBasic, RecordOps, ListLibrary,
    TupleBasics. -/

/-! ## M3 Task 4 — default methods

    A Haskell class default reaches the transpiler as TWO things: `hasDefault` in
    the class-shape channel, and a top-level `$dm<method>` bind holding the body.
    The Lean image is a class-body `:=` default plus instances that OMIT the
    field. This block records the observed spines, the two Lean-side probes that
    settled the emission shape, and the two pre-discovered defects fixed here.

### Observation 1 — the fixture and its `classDecls`

    `examples/haskell/DefaultMethods.hs`: `class Greet a where name :: a -> Int;
    greet :: a -> Int; greet x = name x + 1`, `data Loud = Loud Int` /
    `data Quiet = Quiet Int`, `instance Greet Loud` OVERRIDING `greet`,
    `instance Greet Quiet` RELYING on the default, call sites for both methods at
    both types. `.transpile-sandbox/.decls/DefaultMethods.decls.json`, `classDecls`
    (pretty-printed; both methods share the type `a -> Int`):

        [ { "name": "Greet", "tyVars": ["a"], "supers": [],
            "methods": [ {"name": "name",  "hasDefault": false, "type": …},
                         {"name": "greet", "hasDefault": true,  "type": …} ] } ]

    `hasDefault` discriminates WITHIN one class and in DECLARATION order — the
    first committed fixture to exercise the field (Task 1 could only verify it
    with a throwaway probe).

### Observation 2 — the `$dm` spine, and its ROLE (pre-discovered defect 2)

    `/tmp/transpile-DefaultMethods.json`. Verbatim, BEFORE the shim fix below:

        ### $dmgreet#9094 [role=dict]
        ###   type: ForAll
          Lam (a#8936 [role=tyVar] : Type)
            Lam ($dGreet#9185 [role=dict] : (Greet _v_v8936))
              Lam (x#8937 [role=id] : _v_v8936)
                App
                  App
                    App
                      App
                        Var GHC.Num.+#1300 [role=id] : _Unknown
                        Type Int
                      Var GHC.Num.$fNumInt#9036 [role=dict] : _Unknown
                    App
                      App
                        App
                          Var name#8929 [role=id] : _Unknown
                          Type _v_v8936
                        Var $dGreet#9185 [role=dict] : (Greet _v_v8936)
                      Var x#8937 [role=id] : _v_v8936
                  App
                    Var GHC.Types.I##19 [role=id] : _Unknown
                    Lit {'tag': 'LitInt', 'value': 1}

    `[role=dict]` on `$dmgreet` is the mislabel. It is a method BODY; the shim's
    heuristic (`$d`/`$f` prefix ⇒ dict) has no exemption for `$dm`. The three
    inner lambdas are exactly right, though: the `@a` tyvar and the `$dGreet`
    dictionary binder are erased by `Lower`, as is the dict ARGUMENT of the inner
    `name @a $dGreet x`, leaving `\x -> name x + 1`.

    THE DECISION: fix the SHIM, not the consumer. `role` is a claim about the Id,
    and the claim was false; the exemption is exact rather than a guess, because a
    dictionary's name is `$d` + a CLASS name (always upper-case: `$dGreet`,
    `$dIP`) while `$dm` is followed by a METHOD name (lower-case or symbolic), so
    the two prefixes cannot collide. After `take 3 n == "$dm" -> "id"` in
    `shim/Main.hs`, the same binder re-dumps as:

        ### $dmgreet#9094 [role=id]

    WHY IT MATTERS even though nothing observable changed: at pass-0000 `$dmgreet`
    only ever appears in HEAD position (see observation 3), and `Lower` erases
    dict-role Vars in ARGUMENT position — so the live dump was one inlining away
    from silently deleting a default's body from wherever it was passed. The
    erasure itself is pinned below, and `Main.lean` now warns if a `$dm` binder
    ever arrives with role `dict` again. BLAST RADIUS of the shim change,
    measured: `$dm` occurs in exactly ONE of the 26 saved dumps
    (`grep -o '\$dm[a-zA-Z]*' /tmp/transpile-*.json` ⇒ `DefaultMethods: $dmgreet`),
    so no other fixture's roles can move.

### Observation 3 — the Rec groups (pre-discovered defect 1)

    Both instances' method binds share a Rec group with their dfun, because a
    `$c` body that needs the instance's own dictionary references it:

        Rec group: ['$fGreetLoud', '$cgreet']       -- override calling `name`
        Rec group: ['$fGreetQuiet', '$cgreet']      -- the default wrapper

    The `$f` member is the group HEAD in both. `emitFullProgram` classified a
    whole group by that head, so both groups were dropped as junk while the
    emitted instances still referenced their `$c` defs. The pre-fix build,
    verbatim:

        error: …/DefaultMethods.lean:43:11: Unknown identifier `_dollar_cgreet_9231`
        error: …/DefaultMethods.lean:47:11: Unknown identifier `_dollar_cgreet_9243`

    The RELYING instance's wrapper, post-`Lower` (its `Type Quiet` and
    `$fGreetQuiet` arguments both erased, leaving one Var):

        ###   $cgreet#9231 [role=id]
        ###     type: (Quiet -> Int)
          App
            App
              Var $dmgreet#9094 [role=dict] : _Unknown
              Type Quiet
            Var $fGreetQuiet#9136 [role=dict] : _Unknown

    Fixed by `Emit.filterBinds` (per-pair, like `Main.keepBinding`), which also
    covers the direction GHC has NOT shown us: a `$c`-headed group would have
    EMITTED the `$f` dict-builder. Both orders are guarded below.

### Observation 4 — the Lean-side probes that fixed the emission shape

    (a) A class-body default resolves a SIBLING method by BARE name, and an
    instance omitting the field picks it up:

        class Greet (a : Type) where
          name : a → Int
          greet : a → Int := fun x => name x + 1
        instance : Greet Quiet where          -- no `greet`
          name := cnameQuiet
        example : Greet.greet (Quiet.Quiet 3) = 4 := by decide   -- passes

    (b) The SAME body with the reference QUALIFIED does not elaborate, because the
    class name is not a constant yet inside its own body:

        greet2 : a → Int := fun x => Greet2.name2 x + 1
        -- error: Invalid field `name2`: The environment does not contain
        --   `Function.name2`

    Hence `MethodRef.bare`, set only on the map used for default bodies. Dropping
    the map entry instead would emit `Maps.valueMap`'s BUILTIN for an operator
    method — the silent-wrong this flag exists to avoid.

    (c) A default may only reference methods declared EARLIER in the class body:

        class Fwd (a : Type) where
          g : a → Int := fun x => f x + 1
          f : a → Int
        -- error: Unknown identifier `f`

    Recorded as a LIMITATION, not fixed: `classOpItems` order is declaration
    order, so a Haskell class declaring a defaulted method before the method its
    default calls fails loud. No fixture has that shape.

    (c2) A THIRD loud residual in the same body, found by review and then
    measured: the bare-sibling rewrite fires only when `methodMap` has an entry
    for that sibling, and the map is built from INSTANCES
    (`reconstructClasses`). A class with a default whose sibling has no local
    instance — the plugin channel supplies the `ClassDecl`, the reconstruction
    supplies no entries — emits `name_8929` in the class body, an unbound
    identifier. Loud, unfixtured, and pinned in the guards; the naive fix
    (synthesizing map entries from `ClassDecl.methods`) would trade it for a
    silent-wrong, because `emitVar` is first-match and such entries carry no
    `shadowedBy`, so a local binder named like a method would become the field.

    (d) A FIELDLESS instance is legal (`instance : AllDef T where` with every
    method defaulted), which is why `emitInstanceUser` emits that form instead of
    refusing.

    (e) The wall this task does NOT remove: an instance that OVERRIDES a method
    with a body calling a SIBLING method. GHC's `$cgreet` then needs the
    instance's own dictionary, and the emitted def precedes the instance (Lean
    instances are not forward-visible). Observed after the fix, with the fixture's
    override written as `greet x = name x * 10`:

        def _dollar_cgreet_9243 (x_9077 : Loud) : Int :=
          (((· * ·)) ((Greet.name) (x_9077))) ((10 : Int))
        error: …/DefaultMethods.lean:42:15: failed to synthesize
          Greet ?m.20

    A `mutual` block does NOT rescue it — PROBED: `mutual instance instSibT : Sib T
    where nm := cnmT; gr := cgrT / def cgrT := fun x => Sib.nm x * 10 end` gives
    `error: failed to synthesize Sib T`. The real fix is self-dispatch rewriting
    (a method call through the instance's OWN dfun resolving to the sibling `$c`
    def), which needs the dict argument `Lower` has already erased — a pre-Emit
    pass, out of scope here. The committed fixture therefore overrides by matching
    the constructor (`greet (Loud n) = n * 10`), and the shape above is a HANDOFF:
    Task 5's superclass method calls hit the same wall.

### The emitted result, and what verifies it

    `class Greet (a : Type) where`
    `  name : (a → Int)`
    `  greet : (a → Int) := (fun x_8937 => (((· + ·)) ((name) (x_8937))) ((1 : Int)))`
    `instance : Greet Quiet where`
    `  name := _dollar_cname_9227`            -- `greet` OMITTED
    `instance : Greet Loud where`
    `  name := _dollar_cname_9239`
    `  greet := _dollar_cgreet_9243`          -- the override, wired

    `lake build GhcCoreToLean.Generated.DefaultMethods` is GREEN: all four
    quantified properties ✅ Valid (`loudName_correct`, `quietName_correct`,
    `loudGreet_overrides_the_default` = `n * 10`, `quietGreet_uses_the_default` =
    `n + 1`) plus the ground `override_and_default_differ` by `decide`. The last
    three are what distinguish the two behaviours: no single shared body satisfies
    `n * 10` and `n + 1` at once.

### Guards -/

def m3t4Greet : ClassDecl :=
  { name := "Greet", tyVars := ["a"], supers := [],
    methods := [ { name := "name",  ty := .tyFun (.tyVar "a") (.tyCon "Int" []) },
                 { name := "greet", ty := .tyFun (.tyVar "a") (.tyCon "Int" []),
                   hasDefault := true } ] }

-- The `$dmgreet` bind as `Lower` leaves it: `\x -> name x + 1`, with `name` the
-- class-op selector Var (unique 8929, as in the dump) — see observation 2.
def m3t4NameSel : Var :=
  {name := "name", unique := 8929, ty := .tyCon "_Unknown" [], role := .id}
def m3t4DmBind : Bind :=
  .nonRec {name := "$dmgreet", unique := 9094,
           ty := .tyFun (.tyVar "a") (.tyCon "Int" []), role := .id}
    (.lam {name := "x", unique := 8937, ty := .tyVar "a", role := .id}
      (.app (.app (.var {name := "GHC.Num.+", unique := 1300,
                         ty := .tyCon "_Unknown" [], role := .id})
                  (.app (.var m3t4NameSel)
                        (.var {name := "x", unique := 8937, ty := .tyVar "a", role := .id})))
            (.lit (.litInt 1))))
-- The relying instance's wrapper `$cgreet` (observation 3) and its dfun, in the
-- Rec group GHC put them in; plus the overriding instance's real `$cgreet`.
def m3t4QuietWrapper : Var :=
  {name := "$cgreet", unique := 9231,
   ty := .tyFun (.tyCon "Quiet" []) (.tyCon "Int" []), role := .id}
def m3t4QuietDfun : Var :=
  {name := "$fGreetQuiet", unique := 9136, ty := .tyCon "Greet" [.tyCon "Quiet" []],
   role := .dict}
-- The wrapper's body as `Lower` leaves it. The dump has `($dmgreet @Quiet)
-- $fGreetQuiet` (DefaultMethods `/binds/26/pairs/1/rhs`); the type argument and
-- the dict argument both erase, leaving the bare `$dmgreet` reference.
--
-- `role := .id` is the OBSERVED role at that reference, not an assumption — but
-- only since the `$dm` exemption was added to `convertExternalName` as well as
-- `binderRole`. Before that the dump read `"dict"` HERE while the binder at
-- `/binds/4` read `"id"`; the tripwire below now scans references for exactly
-- that split.
def m3t4DmRef : Expr :=
  .var {name := "$dmgreet", unique := 9094, ty := .tyCon "_Unknown" [], role := .id}
-- The dfun's body is the observed one, `C:Greet @Quiet $cname $cgreet` with its
-- type argument erased by `Lower`: it must reference BOTH `$c` binds, since that
-- is what `reconstructClasses` reads the method→class map out of.
def m3t4QuietDfunRhs : Expr :=
  .app (.app (.var {name := "C:Greet", unique := 9097,
                    ty := .tyCon "_Unknown" [], role := .id})
             (.var {name := "$cname", unique := 9227,
                    ty := .tyFun (.tyCon "Quiet" []) (.tyCon "Int" []), role := .id}))
       (.var m3t4QuietWrapper)
def m3t4QuietRec : Bind :=
  .rec_ [ (m3t4QuietDfun, m3t4QuietDfunRhs), (m3t4QuietWrapper, m3t4DmRef) ]
def m3t4CnameQuiet : Bind :=
  .nonRec {name := "$cname", unique := 9227,
           ty := .tyFun (.tyCon "Quiet" []) (.tyCon "Int" []), role := .id}
    (.lam {name := "ds", unique := 9286, ty := .tyCon "Quiet" [], role := .id}
      (.lit (.litInt 0)))
def m3t4CgreetLoud : Bind :=
  .nonRec {name := "$cgreet", unique := 9243,
           ty := .tyFun (.tyCon "Loud" []) (.tyCon "Int" []), role := .id}
    (.lam {name := "ds", unique := 9363, ty := .tyCon "Loud" [], role := .id}
      (.lit (.litInt 7)))
def m3t4CnameLoud : Bind :=
  .nonRec {name := "$cname", unique := 9239,
           ty := .tyFun (.tyCon "Loud" []) (.tyCon "Int" []), role := .id}
    (.lam {name := "ds", unique := 9362, ty := .tyCon "Loud" [], role := .id}
      (.lit (.litInt 0)))
def m3t4QuietInst : Instance :=
  {className := "Greet", headTypes := [.tyCon "Quiet" []], dfunName := "$fGreetQuiet",
   dfunUnique := 9136}
def m3t4LoudInst : Instance :=
  {className := "Greet", headTypes := [.tyCon "Loud" []], dfunName := "$fGreetLoud",
   dfunUnique := 9122}
def m3t4Binds : CoreProgram := [m3t4QuietRec, m3t4DmBind, m3t4CnameQuiet, m3t4CnameLoud, m3t4CgreetLoud]
def m3t4Mm : List MethodRef :=
  [{ method := "name", cls := "Greet" }, { method := "greet", cls := "Greet" }]

-- THE KEY. Both halves are required, and each alone is not enough: `hasDefault`
-- without the `$dm` bind (a filtered or absent body) and the `$dm` bind without
-- `hasDefault` (the no-plugin path, where the class shape is reconstructed from
-- instances and cannot know) BOTH yield no translated default — which is what
-- keeps every pre-existing behaviour for those two shapes.
#guard translatedDefaults m3t4Binds [m3t4Greet] == [("Greet", "greet")]
#guard translatedDefaults [m3t4CnameQuiet] [m3t4Greet] == ([] : List (Name × Name))
#guard translatedDefaults m3t4Binds
         [{ m3t4Greet with methods := m3t4Greet.methods.map ({ · with hasDefault := false }) }]
         == ([] : List (Name × Name))

-- THE DEFAULT BODY, character-exact, with the sibling reference BARE — the shape
-- probe (b) showed is the only one that elaborates inside a class body.
#guard classDefaultBody m3t4Mm [] m3t4Binds m3t4Greet "greet"
         == some "(fun x_8937 => (((· + ·)) ((name) (x_8937))) ((1 : Int)))"
-- …and the flag is SCOPED to the class's own methods: a same-named method of
-- ANOTHER class stays qualified, because that reference is not a sibling.
#guard classDefaultBody [{ method := "name", cls := "Other" }] [] m3t4Binds m3t4Greet "greet"
         == some "(fun x_8937 => (((· + ·)) ((Other.name) (x_8937))) ((1 : Int)))"
-- THE RESIDUAL, measured: the bare rewrite needs a map ENTRY for the sibling,
-- and the map is instance-driven. With none (a class whose default's sibling has
-- no local instance, or whose `$c` bind was filtered) the body emits
-- `name_8929` — an unbound identifier inside the class body, so LOUD. Pinned as
-- the degradation it is, not as intended output; see `MethodRef.bare` for why
-- synthesizing entries from `ClassDecl.methods` would be worse than this.
#guard classDefaultBody [] [] m3t4Binds m3t4Greet "greet"
         == some "(fun x_8937 => (((· + ·)) ((name_8929) (x_8937))) ((1 : Int)))"
#guard classDefaultBody [{ method := "greet", cls := "Greet" }] [] m3t4Binds m3t4Greet "greet"
         == some "(fun x_8937 => (((· + ·)) ((name_8929) (x_8937))) ((1 : Int)))"
-- Both directions of `MethodRef.bare` at the `emitVar` level.
#guard emitVar [{ method := "name", cls := "Greet", bare := true }] [] m3t4NameSel == "name"
#guard emitVar [{ method := "name", cls := "Greet" }] [] m3t4NameSel == "Greet.name"
-- `bare` does not outrank `shadowedBy`: a LOCAL binder of that name is still a
-- local, inside a default body as anywhere else.
#guard emitVar [{ method := "name", cls := "Greet", bare := true, shadowedBy := [8929] }] []
         m3t4NameSel == "name_8929"

-- THE CLASS BLOCK. Defaulted method carries `:=`, the plain one does not.
#guard emitClassDecl [("greet", "(fun x => name x + 1)")] m3t4Greet
         == "class Greet (a : Type) where\n  name : (a → Int)\n" ++
            "  greet : (a → Int) := (fun x => name x + 1)"
#guard emitClassDecl [] m3t4Greet
         == "class Greet (a : Type) where\n  name : (a → Int)\n  greet : (a → Int)"

-- THE WRAPPER TEST, tight (observation 3): exactly a `$dm<method>` Var.
#guard isDefaultWrapperBody "greet" (.var {name := "$dmgreet", unique := 9094,
                                           ty := .tyCon "_Unknown" [], role := .id}) == true
-- wrong method, an eta-expanded wrapper, and an ordinary body all say false —
-- the last two then emit as ordinary fields and fail loud, never silently
-- adopting the default.
#guard isDefaultWrapperBody "name" (.var {name := "$dmgreet", unique := 9094,
                                          ty := .tyCon "_Unknown" [], role := .id}) == false
#guard isDefaultWrapperBody "greet"
         (.lam {name := "x", unique := 1, ty := .tyCon "Quiet" [], role := .id}
           (.app (.var {name := "$dmgreet", unique := 9094,
                        ty := .tyCon "_Unknown" [], role := .id})
                 (.var {name := "x", unique := 1, ty := .tyCon "Quiet" [], role := .id})))
         == false

-- THE THREE FATES, on the observed binds.
def m3t4Defaults : List (Name × Name) := [("Greet", "greet")]
def m3t4GreetM : ClassMethod := m3t4Greet.methods.getLast!
def m3t4NameM  : ClassMethod := m3t4Greet.methods.head!
#guard classifyInstanceMethod m3t4Defaults m3t4Binds "Greet"
         (emitType (.tyCon "Quiet" [])) m3t4GreetM == .fromDefault
#guard classifyInstanceMethod m3t4Defaults m3t4Binds "Greet"
         (emitType (.tyCon "Loud" [])) m3t4GreetM == .field "_dollar_cgreet_9243"
#guard classifyInstanceMethod m3t4Defaults m3t4Binds "Greet"
         (emitType (.tyCon "Quiet" [])) m3t4NameM == .field "_dollar_cname_9227"
-- No `$c` bind AND no translated default → unresolved (the instance is skipped).
#guard classifyInstanceMethod [] m3t4Binds "Greet"
         (emitType (.tyCon "Bag" [])) m3t4NameM == .unresolved
-- No `$c` bind but a translated default → filled by the class body. This is the
-- arm the plan predicted GHC would take; GHC actually emits a wrapper, so the
-- arm is REACHED only through the `.fromDefault` case above. Pinned anyway: it is
-- the behaviour a future GHC that omits the wrapper would need.
#guard classifyInstanceMethod m3t4Defaults m3t4Binds "Greet"
         (emitType (.tyCon "Bag" [])) m3t4GreetM == .fromDefault

-- THE INSTANCE, both instances of the fixture. The relying one omits `greet`…
#guard emitInstanceUser m3t4Defaults [m3t4Greet] m3t4Binds m3t4QuietInst
         == some ("instance : Greet (GHCCore.tyConOpaque \"Quiet\") where\n" ++
                 "  name := _dollar_cname_9227")
-- …and the overriding one wires it.
#guard emitInstanceUser m3t4Defaults [m3t4Greet] m3t4Binds m3t4LoudInst
         == some ("instance : Greet (GHCCore.tyConOpaque \"Loud\") where\n" ++
                 "  name := _dollar_cname_9239\n  greet := _dollar_cgreet_9243")
-- WITHOUT the default translated, the same wrapper is wired as a field — the
-- no-plugin path, whose reference to the (then still emitted) `$dmgreet` def is
-- loud, not silent.
#guard emitInstanceUser [] [m3t4Greet] m3t4Binds m3t4QuietInst
         == some ("instance : Greet (GHCCore.tyConOpaque \"Quiet\") where\n" ++
                 "  name := _dollar_cname_9227\n  greet := _dollar_cgreet_9231")
-- A method with NO default and no bind kills the whole instance (unchanged), and
-- is now REPORTED rather than silent.
#guard emitInstanceUser m3t4Defaults [m3t4Greet] [m3t4QuietRec, m3t4DmBind] m3t4QuietInst == none
#guard unresolvedInstanceMethods
         { binds := [m3t4QuietRec, m3t4DmBind], typeDecls := [], instances := [m3t4QuietInst],
           classDecls := [m3t4Greet] }
         == [("Greet", "Quiet", "name")]
#guard ((unresolvedInstanceMethodWarning "Greet" "Quiet" "name").splitOn
          "instance `Greet Quiet` is DROPPED: its method `name` resolves to nothing").length == 2
-- Every method defaulted and none overridden → a FIELDLESS instance (probe (d)).
#guard emitInstanceUser [("Greet", "greet")] [{ m3t4Greet with methods := [m3t4GreetM] }]
         m3t4Binds m3t4QuietInst
         == some "instance : Greet (GHCCore.tyConOpaque \"Quiet\") where"
-- A builtin-class instance contributes nothing here: no `ClassDecl` is built for
-- `Eq`/`Ord`/`Show`, so the diagnostic cannot fire on the paths that legitimately
-- drop their `$c` binds.
#guard unresolvedInstanceMethods
         { binds := m3t4Binds, typeDecls := [], instances := [eqInst, ordInst, showInst],
           classDecls := [m3t4Greet] }
         == ([] : List (Name × String × Name))

-- REC-PAIR SURVIVAL, the fix for defect 1 — and its ORDER-INDEPENDENCE, which is
-- the whole point: the `$c` member survives and the `$f` member does not,
-- whichever GHC lists first.
def m3t4bindNames : Bind → List Name
  | .nonRec v _ => [v.name]
  | .rec_ ps    => ps.map (·.1.name)
def m3t4QuietRecFlipped : Bind :=
  .rec_ [ (m3t4QuietWrapper, m3t4DmRef), (m3t4QuietDfun, m3t4QuietDfunRhs) ]
#guard (filterBinds (fun v _ => v.name.startsWith "$c") [m3t4QuietRec]).flatMap m3t4bindNames
         == ["$cgreet"]
#guard (filterBinds (fun v _ => v.name.startsWith "$c") [m3t4QuietRecFlipped]).flatMap m3t4bindNames
         == ["$cgreet"]
#guard (filterBinds (fun v _ => !v.name.startsWith "$f") [m3t4QuietRec]).flatMap m3t4bindNames
         == ["$cgreet"]
#guard (filterBinds (fun v _ => !v.name.startsWith "$f") [m3t4QuietRecFlipped]).flatMap m3t4bindNames
         == ["$cgreet"]
-- A group nothing survives in disappears; a group everything survives in is
-- unchanged (so a genuine multi-binding `mutual` still emits as one).
#guard (filterBinds (fun v _ => v.name.startsWith "zzz") [m3t4QuietRec]).isEmpty
#guard (filterBinds (fun _ _ => true) [m3t4QuietRec]).flatMap m3t4bindNames
         == ["$fGreetQuiet", "$cgreet"]
-- The predicate sees the BODY too, which is what the wrapper drop needs.
#guard (filterBinds (fun v e => !(v.name == "$cgreet" && isDefaultWrapperBody "greet" e))
         [m3t4QuietRec]).flatMap m3t4bindNames == ["$fGreetQuiet"]

-- WHOLE-PIPELINE, the three suppressions at once — and again, order-independent.
def m3t4Prog (rec_ : Bind) : Program :=
  { binds := [rec_, m3t4DmBind, m3t4CnameQuiet], typeDecls := [],
    instances := [m3t4QuietInst], classDecls := [m3t4Greet] }
def m3t4Out : String := emitFullProgram [] (m3t4Prog m3t4QuietRec)
#guard m3t4Out == emitFullProgram [] (m3t4Prog m3t4QuietRecFlipped)
-- the class-body default, translated from the `$dm` body…
#guard (m3t4Out.splitOn
  "  greet : (a → Int) := (fun x_8937 => (((· + ·)) ((name) (x_8937))) ((1 : Int)))").length == 2
-- …the instance without the defaulted field…
#guard (m3t4Out.splitOn ("instance : Greet (GHCCore.tyConOpaque \"Quiet\") where\n" ++
                         "  name := _dollar_cname_9227")).length == 2
-- …and NEITHER the `$dm` def nor the wrapper `$c` def anywhere (they have no
-- second Lean image; each would be a duplicate or an unbound reference).
#guard (m3t4Out.splitOn "_dollar_dmgreet").length == 1
#guard (m3t4Out.splitOn "_dollar_cgreet").length == 1
-- The `$f` dict-builder is still never emitted, in either order.
#guard (m3t4Out.splitOn "_dollar_fGreetQuiet").length == 1

-- `$dm` ROLE TRIPWIRE (observation 2). The shim writes the `$d`/`$f` prefix rule
-- TWICE — `binderRole` for binders, `convertExternalName` for references — and
-- GHC routes a top-level name through `EVarGlobal` even inside its own module, so
-- the two classify different halves of the same name. Both now exempt `$dm`; the
-- first fix touched `binderRole` only, and the DefaultMethods dump then said
-- `role: "id"` at the binder (`/binds/4`) and `role: "dict"` at its one reference
-- (`/binds/26/pairs/1/rhs/fun/fun`). Post-fix that reference reads `"id"`, which
-- is what `m3t4DmRef` below encodes — observed, not assumed.
--
-- Three things pinned here: the detector on a BINDER, the detector on a
-- REFERENCE inside a body (the half a binders-only scan missed), and the erasure
-- that makes either matter.
def m3t4DmDictBind : Bind :=
  .nonRec {name := "$dmgreet", unique := 9094,
           ty := .tyFun (.tyVar "a") (.tyCon "Int" []), role := .dict} (.lit (.litInt 0))
#guard dmVarsMislabelledAsDicts [m3t4DmDictBind] == ["$dmgreet"]
#guard dmVarsMislabelledAsDicts m3t4Binds == ([] : List Name)
def m3t4DmDictRec : Bind :=
  .rec_ [ ({name := "$dmgreet", unique := 1, ty := .tyCon "Int" [], role := .dict},
           .lit (.litInt 0)) ]
#guard dmVarsMislabelledAsDicts [m3t4DmDictRec] == ["$dmgreet"]
-- THE REFERENCE HALF, in the shape the dump actually had: an `id`-role `$cgreet`
-- binder whose BODY applies the dict-role `$dmgreet` — unlowered, as `Main.lean`
-- scans it (`prog.binds`, pre-`Lower`: lowering would already have deleted the
-- occurrence). The binder is clean, so a binders-only scan reports nothing.
def m3t4DmDictRefBody : Expr :=
  .app (.app (.var {name := "$dmgreet", unique := 9094,
                    ty := .tyCon "_Unknown" [], role := .dict})
             (.type_ (.tyCon "Quiet" [])))
       (.var m3t4QuietDfun)
def m3t4DmDictRefBind : Bind := .nonRec m3t4QuietWrapper m3t4DmDictRefBody
#guard dmVarsMislabelledAsDicts [m3t4DmDictRefBind] == ["$dmgreet"]
-- Same body inside a Rec group, and inside a `let` — the nesting the walker has
-- to reach, and the shape `$cgreet` is really in (`/binds/26` is a Rec).
#guard dmVarsMislabelledAsDicts
         [.rec_ [(m3t4QuietDfun, m3t4QuietDfunRhs), (m3t4QuietWrapper, m3t4DmDictRefBody)]]
         == ["$dmgreet"]
#guard dmVarsMislabelledAsDicts
         [.nonRec m3t4QuietWrapper
            (.let_ (.nonRec m3t4QuietWrapper m3t4DmDictRefBody) (.lit (.litInt 0)))]
         == ["$dmgreet"]
-- Duplicates collapse: `Main.lean` prints one warning per entry.
#guard dmVarsMislabelledAsDicts [m3t4DmDictRefBind, m3t4DmDictBind] == ["$dmgreet"]
-- And the post-fix reference role is NOT reported (this is the observed dump).
#guard dmVarsMislabelledAsDicts [.nonRec m3t4QuietWrapper m3t4DmRef] == ([] : List Name)
-- THE TRAP ITSELF: a dict-role `$dm` reference in ARGUMENT position is erased —
-- the reason a mislabelled reference is a miscompile and not a cosmetic defect.
-- (The observed reference sits in HEAD position, which `isTypeOrDictArg` never
-- inspects, so today's dump would not have miscompiled; nothing pinned it there,
-- which is why the tripwire now watches references at all.)
#guard emitExpr [] [] (Lower.lowerExpr
         (.app (.var {name := "f", unique := 1, ty := .tyCon "_Unknown" [], role := .id})
               (.var {name := "$dmgreet", unique := 9094,
                      ty := .tyCon "_Unknown" [], role := .dict}))) == "f_1"
-- …and with the role the shim now emits at references, it survives (loud if
-- unbound, never gone).
#guard emitExpr [] [] (Lower.lowerExpr
         (.app (.var {name := "f", unique := 1, ty := .tyCon "_Unknown" [], role := .id})
               (.var {name := "$dmgreet", unique := 9094,
                      ty := .tyCon "_Unknown" [], role := .id})))
         == "(f_1) (_dollar_dmgreet_9094)"
-- Head position, both roles: the emission is the same either way — which is why
-- fixing the shim's reference role changed no generated file.
#guard emitExpr [] [] (Lower.lowerExpr
         (.app (.app (.var {name := "$dmgreet", unique := 9094,
                            ty := .tyCon "_Unknown" [], role := .dict})
                     (.type_ (.tyCon "Quiet" [])))
               (.var m3t4QuietDfun)))
         == emitExpr [] [] (Lower.lowerExpr
         (.app (.app (.var {name := "$dmgreet", unique := 9094,
                            ty := .tyCon "_Unknown" [], role := .id})
                     (.type_ (.tyCon "Quiet" [])))
               (.var m3t4QuietDfun)))

-- `$cshow` SCOPING, both directions (`Main.isGhcRuntimePlumbing` delegates here).
-- `Show`'s three methods are dropped…
#guard isDerivedShowMethod "$cshow" == true
#guard isDerivedShowMethod "$cshowsPrec" == true
#guard isDerivedShowMethod "$cshowList" == true
-- …and a user class's `show`-PREFIXED method is not: `$cshowIt` was eaten by the
-- old prefix test, which cost the whole instance (the all-or-nothing skip).
#guard isDerivedShowMethod "$cshowIt" == false
#guard isDerivedShowMethod "$cshows" == false
#guard isDerivedShowMethod "$cshowMe" == false
-- Not a `$c` bind at all → not this rule's business (the `$fShow`/`$sshow`
-- prefixes in `Main.lean` still handle those).
#guard isDerivedShowMethod "$fShowBox" == false
#guard isDerivedShowMethod "$sshow" == false

/-! ### Regression — what this task could have moved, and what it did

    The at-risk change is `filterBinds`: every multi-member Rec group in the
    corpus mixes an `$f` dfun with `$c` method binds, so a group whose `$c` half
    is NOT otherwise suppressed now EMITS that half where the head-name test
    dropped it. Enumerated from the saved dumps rather than guessed —
    `Arithmetic` and `Ratio` (`['$fShow…', '$cshowList', '$cshow']`,
    `['$fEq…', '$c/=']`), `OrdInstance` and `ZZCoherence`
    (`['$fOrd…', '$cmax', '$c>=', '$c>', '$cmin', '$c<=']`), `NewtypeInstances`,
    `UserClassNeq*`. In every one of them the `$c` half is already filtered
    earlier — by `Main.lean`'s Show/`$c/=` rules or by `isSuppressedMethod`'s
    derived-Eq/Ord head match — so the group still contributes nothing.

    MEASURED, not argued: the 26 saved shim dumps in `/tmp` were re-emitted with
    the pre-change binary (`git stash` of Emit/Main/Unit/shim, rebuild) and the
    post-change one, same env for both. `DefaultMethods.lean` is the ONLY emitted
    file that differs; the other 25 are byte-identical, and the 5 refusal
    fixtures still refuse with identical messages. Scope of that run: no
    `LEAN_SPEC_DIR`, so it compares the EMITTED CODE and not the spec text — the
    spec path (`resolveSpecText`) is untouched by this task. The full pipeline
    (`./transpile.sh`, specs included) was then re-run on `UserClass`, `Ratio` and
    `TwoClassesDistinctMethods`: byte-identical to their pre-change files.

    ONE stderr line moved, deliberately: `SuperClass.hs` now emits the
    `unresolvedInstanceMethods` warning for `Container Bag`'s `empty` and
    `insert`. That is the drop Task 1's observation 4 recorded as silent, and its
    cause is the third one the message lists — neither method's type STARTS with
    the class parameter (`$cempty : Bag`, `$cinsert : (Int -> (Bag -> Bag))`), so
    `findClassMethodBind` cannot attribute either bind to the instance. Nothing
    about SuperClass's emitted output changed. -/

/-! ## M3 Task 5 — superclasses

    Two mechanisms, because Lean forced two. `class Sized a => Container a` emits
    as `extends`; `class Ord a => Capped a` CANNOT, and its binder recipe is
    injected at every constraint site instead. Everything below that reads like a
    design decision was made by a probe first.

### Lean-side probes

    Each is a scratch file run with `lake env lean` (Lean 4 v4.24.0, this
    repo's toolchain). Replies verbatim; the Blaster "local changes" warning is
    elided throughout.

    (a) `extends` + an instance that OMITS the parent field. The emitter's
    `emitInstanceUser` writes only the class's OWN methods, so the question was
    whether Lean accepts that or demands `toSized := …`:

        class Sized (a : Type) where
          size : a → Int
        class Container (a : Type) extends Sized a where
          empty : a
          insert : Int → a → a
        inductive Bag where | Bag (n : Int)
        instance : Sized Bag where
          size := fun b => match b with | .Bag n => n
        instance : Container Bag where
          empty := Bag.Bag 0
          insert := fun k b => match b with | .Bag n => Bag.Bag (n + k)

    → EXIT 0. Lean fills the parent field from the `Sized Bag` instance in scope,
    so the emitted instance shape needs no change at all. NEGATIVE control, same
    file with the `Sized Bag` instance deleted:

        error: Fields missing: `size`

    i.e. a missing parent instance is LOUD, and it is loud in the FLATTENED
    spelling — Lean asks for the parent's fields, not for `toSized`. That message
    is the one `sortInstances` exists to prevent (see the ordering section below).

    (b) the parent's method under only the CHILD's constraint, spelled the way
    `methodMap` spells it:

        def sizeViaContainer {t : Type} [Container t] : (t → Int) :=
          fun x => (Sized.size) (x)
        def bagSize : (Bag → Int) := sizeViaContainer
        def bagInsert : (Int → (Bag → Bag)) := Container.insert

    → EXIT 0. `extends` is what makes `Sized` reachable from `[Container t]`, and
    this is character-for-character the header and body the transpiler already
    emitted before this task (`Generated/SuperClass.lean`, which failed with
    `failed to synthesize Sized t_v9077`): the CLASS was the only thing missing.

    (c) the builtin parent. `Maps.classConMap "Ord"` is EIGHT binder templates,
    and all three ways of putting them inside a `class` were tried.

    (c1) `extends` over the whole recipe:

        class Capped (a : Type) extends Ord a, LT a, LE a, DecidableLT a, DecidableLE a,
                                        Min a, Max a, BEq a where
          cap : a → a → a

        error: expected structure

    at the column of `DecidableLT a`. `DecidableLT α` is a `def` (it unfolds to
    `DecidableRel (· < ·)`, a Pi type), and `extends` takes structures only. This
    is a HARD elimination of the shape, not a preference.

    (c2) the plan's other candidate — instance-implicit FIELDS:

        class Capped (a : Type) where
          [ordInst : Ord a]
          [ltInst : LT a]
          … [beqInst : BEq a]
          cap : a → a → a

    The class DECLARATION elaborates (the `[f : T]` field binder is legal), and
    `Capped.cap` works, but the fields are not registered as instances:

        error: failed to synthesize LT t      -- def clampLt … [Capped t] … decide (x < y)
        error: failed to synthesize Min t     -- def useMin  … [Capped t] … Min.min x y
        error: failed to synthesize BEq t     -- def useBEq  … [Capped t] … x == y

    So instance-implicit fields do NOT compose out of a child constraint. (c3) the
    same eight as instance-implicit class PARAMETERS elaborates as a declaration
    too, but then `Capped t` itself needs the eight in scope to even be written —
    it moves the problem to every constraint site without removing it.

    (c4) `extends` over only the six recipe entries that ARE structures (`Ord`,
    `LT`, `LE`, `Min`, `Max`, `BEq`) — the near miss, and the one that pins the
    residue exactly:

        class Capped (a : Type) extends Ord a, LT a, LE a, Min a, Max a, BEq a where
          cap : a → a → a
        def useLt {t : Type} [Capped t] : t → t → Bool := fun x y => decide (x < y)

        error: failed to synthesize Decidable (x < y)

    ONE error, and only about `Decidable`: `x < y`, `Min.min`, `==`, `compare`,
    `Capped.cap` and the `instance : Capped Meters` all elaborated. So `extends`
    composes fine — it simply cannot carry the two `Decidable*` entries, which are
    exactly what the emitter's `decide (a < b)` image of Haskell `<` needs.

    (c5) THE MECHANISM CHOSEN — the recipe at the constraint site, with the class
    carrying no parent at all:

        class Capped (a : Type) where
          cap : a → a → a
        def useAll {t : Type} [Ord t] [LT t] [LE t] [DecidableLT t] [DecidableLE t]
                   [Min t] [Max t] [BEq t] [Capped t] : t → t → Bool :=
          fun x y => decide (x < y) || (x == y) || (Capped.cap x y == Min.min x y)
        inductive Meters where | Meters : Int → Meters
        deriving Repr, Inhabited, DecidableEq, Ord
        instance : LE Meters := leOfOrd
        instance : LT Meters := ltOfOrd
        instance : Min Meters := minOfLe
        instance : Max Meters := maxOfLe
        instance : Capped Meters where cap := fun x y => Min.min x y
        def metersAll : Meters → Meters → Bool := useAll
        example : metersAll (Meters.Meters 3) (Meters.Meters 5) = true := by decide

    → EXIT 0, no output. Two things at once: the eight binders compose with
    `[Capped t]`, AND the whole set synthesizes at a USER data type from nothing
    but what `emitDataDecl` already emits for a derived `Ord` — including
    `DecidableLT Meters`/`DecidableLE Meters`, which come from `LT := ltOfOrd`
    being Bool-backed and hence decidable. Uniform over `Eq`, `Ord` and `Num`
    (no structure-ness test anywhere), which is why it beat the hybrid.

    (d) THE GATE — `blaster` through the `extends` projection, which is what the
    fixture's properties actually need and which (b) did not test. The full
    expected post-fix output was hand-assembled and run before the emitter was
    touched; through TWO projections (`sizeViaContainer` → `Container.toSized` →
    `instSizedBag` → `_dollar_csize`):

        theorem bagSize_correct : ∀ (n : Int), bagSize (Bag.Bag n) = n := by blaster
        theorem bagInsert_adds : ∀ (k n : Int),
          bagInsert k (Bag.Bag n) = Bag.Bag (n + k) := by blaster
        theorem metersCap_min : ∀ (a b : Int), … := by blaster
        theorem metersLt_lt : ∀ (a b : Int), … := by blaster

    → four `✅ Valid`. The one FAILURE in that probe was mine, not the design's:
    `(Container.empty : Bag) = Bag.Bag 0 := by decide` gives `failed to synthesize
    Decidable (…)` because `Bag` derives no `Eq` in the fixture, so the property is
    written `by rfl` (which passes). Recorded because it is why one fixture
    property uses `rfl` where the others use `decide`.

### The dfun spines, and why attribution is positional

    `dfunMethodBinds` reads a method's bind out of the instance's DICTIONARY. Both
    shapes it handles are from `/tmp/transpile-SuperClass.json` (the extended
    fixture; uniques from that run):

        $fSizedBag    = Var $csize                                  -- newtype dict
        $fContainerBag = C:Container @Bag $fSizedBag $cempty $cinsert
        $fCappedLevel  = C:Capped    @Level $fOrdLevel  $ccap

    The second and third are the general shape: dictionary constructor, type
    args, one arg per SUPERCLASS dict (`role = dict` — `$fSizedBag` for a user
    parent, `$fOrdLevel` for a BUILTIN one, stored identically), then the methods.
    The first is what a one-method superclass-free class compiles to: the
    dictionary is a newtype over the method, so the dfun body IS the method Var,
    with no constructor and no cast at pass-0000. `dfunMethodBinds` deliberately
    does NOT strip casts, and that is not an omission to "fix" speculatively: if a
    later pass ever wraps the body, the shape is unrecognized, the attribution
    DECLINES, and the old first-value-argument matcher runs — degrading to today's
    behaviour (and at worst to the loud instance drop), never to a mis-pairing.

    `$cempty : Bag` and `$cinsert : (Int -> (Bag -> Bag))` are precisely the two
    binds `findClassMethodBind`'s first-value-argument match cannot attribute, and
    the whole `Container Bag` instance was dropped for it (M3 Task 1's observation
    4). The dictionary knows the answer positionally.

    The NAME GUARD (`arg.name == "$c" ++ method.name`, all-or-nothing per
    instance) is the reason a positional read is safe to ship: field order equals
    `classOpItems` order is a claim about GHC's internals, and if it ever broke,
    unguarded position would attribute `empty`'s body to `insert` — silently wrong.
    Guarded, any disagreement falls back to the old matcher and at worst drops the
    instance with the existing warning. It costs nothing on real dumps: GHC does
    not suffix these names per instance (two instances of one class both bind
    `$c<method>`), which is also why the bind lookup matches name AND unique. -/

-- The observed class shapes, from the `classDecls` channel of the same run
-- (`supers` for a builtin parent is the bare occurrence name, `"Ord"`, which is
-- the spelling `Maps.classConMap` already keys on):
--
--   [{"name":"Capped","supers":["Ord"],"tyVars":["a"]}
--   ,{"name":"Container","supers":["Sized"],"tyVars":["a"]}
--   ,{"name":"Sized","supers":[],"tyVars":["a"]}]
def m3t5Sized : ClassDecl :=
  { name := "Sized", tyVars := ["a"], supers := [],
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
def m3t5Container : ClassDecl :=
  { name := "Container", tyVars := ["a"], supers := ["Sized"],
    methods := [ { name := "empty",  ty := .tyVar "a" },
                 { name := "insert", ty := .tyFun (.tyCon "Int" [])
                                            (.tyFun (.tyVar "a") (.tyVar "a")) } ] }
def m3t5Capped : ClassDecl :=
  { name := "Capped", tyVars := ["a"], supers := ["Ord"],
    methods := [ { name := "cap", ty := .tyFun (.tyVar "a") (.tyFun (.tyVar "a") (.tyVar "a")) } ] }
-- Plugin order, verbatim: REVERSE declaration order, child before parent.
def m3t5Plugin : List ClassDecl := [m3t5Capped, m3t5Container, m3t5Sized]

/-! ### `emitClassDecl` — the `extends` clause -/

-- A user parent, with the class list that says `Sized` is one of ours.
#guard emitClassDecl [] m3t5Container ["Sized", "Container", "Capped"]
         == "class Container (a : Type) extends Sized a where\n" ++
            "  empty : a\n  insert : (Int → (a → a))"
-- The same class WITHOUT that knowledge (the no-plugin path, and every call site
-- that predates this task) emits exactly the pre-Task-5 string.
#guard emitClassDecl [] m3t5Container
         == "class Container (a : Type) where\n  empty : a\n  insert : (Int → (a → a))"
-- A BUILTIN parent contributes NOTHING to the header: `Ord` is not a user class,
-- and `extends Ord a` cannot carry the recipe (probe (c1)).
#guard emitClassDecl [] m3t5Capped ["Capped"]
         == "class Capped (a : Type) where\n  cap : (a → (a → a))"
-- Two user parents → one `extends`, comma-separated, in `supers` order.
#guard emitClassDecl [] { m3t5Container with supers := ["Sized", "Named"] } ["Sized", "Named"]
         == "class Container (a : Type) extends Sized a, Named a where\n" ++
            "  empty : a\n  insert : (Int → (a → a))"
-- MULTI-PARAMETER: no `extends` at all, because `supers` does not say WHICH
-- parameter the parent constrains. Loud at the use site; a guess would be silent.
#guard emitClassDecl [] { m3t5Container with tyVars := ["a", "b"] } ["Sized", "Container"]
         == "class Container (a : Type) (b : Type) where\n" ++
            "  empty : a\n  insert : (Int → (a → a))"
-- Defaults and `extends` are independent and compose on one class.
#guard emitClassDecl [("empty", "(Bag.Bag 0)")] m3t5Container ["Sized"]
         == "class Container (a : Type) extends Sized a where\n" ++
            "  empty : a := (Bag.Bag 0)\n  insert : (Int → (a → a))"

/-! ### `sortClassDecls` — parent before child -/

-- THE CASE THAT MATTERS: the plugin's reverse order, sorted. `Capped` keeps its
-- place (its only parent is builtin, so it has no local dependency at all).
#guard (sortClassDecls m3t5Plugin).map (·.name) == ["Capped", "Sized", "Container"]
-- Already-correct input is UNCHANGED — the stability that keeps every
-- superclass-free fixture byte-identical.
#guard (sortClassDecls [m3t5Sized, m3t5Container]).map (·.name) == ["Sized", "Container"]
#guard (sortClassDecls [m3t5Capped]).map (·.name) == ["Capped"]
#guard (sortClassDecls ([] : List ClassDecl)).length == 0
-- A three-level chain, worst-case order in: C extends P extends Q.
#guard (sortClassDecls
          [ { m3t5Sized with name := "C", supers := ["P"] },
            { m3t5Sized with name := "P", supers := ["Q"] },
            { m3t5Sized with name := "Q", supers := [] } ]).map (·.name)
         == ["Q", "P", "C"]
-- A superclass GHC would have rejected (a cycle) is not sorted into a lie: the
-- blocked remainder is appended in dump order and Lean fails loud on the forward
-- `extends`. Length is preserved, which is what the totality fallback checks.
#guard (sortClassDecls
          [ { m3t5Sized with name := "C", supers := ["P"] },
            { m3t5Sized with name := "P", supers := ["C"] } ]).length == 2
-- A super naming a class that is NOT local (imported, or builtin) is not a
-- dependency and cannot block: `Capped`'s `Ord` never appears in the class list.
#guard (sortClassDecls [m3t5Capped, m3t5Sized]).map (·.name) == ["Capped", "Sized"]

/-! ### `classSuperBinders` — the builtin recipes, transitively -/

-- `Ord`'s eight, in `Maps.classConMap` order (which is load-bearing: `DecidableLT`
-- after `LT`), with `{t}` still unsubstituted.
#guard classSuperBinders [m3t5Capped]
         == [("Capped", ["[Ord {t}]", "[LT {t}]", "[LE {t}]", "[DecidableLT {t}]",
                         "[DecidableLE {t}]", "[Min {t}]", "[Max {t}]", "[BEq {t}]"])]
-- A USER parent contributes nothing of its own, so a class whose only parent is a
-- user class is ABSENT from the list (not present-with-`[]`): `extends` already
-- carries it.
#guard classSuperBinders [m3t5Sized, m3t5Container] == ([] : List (Name × List String))
-- The whole fixture's class set: only `Capped` has an entry.
#guard (classSuperBinders m3t5Plugin).map (·.1) == ["Capped"]
-- TRANSITIVE through a user parent — the arm no fixture reaches, since it needs a
-- two-level hierarchy whose TOP has a builtin parent. `class Ord a => P a` and
-- `class P a => C a`: `extends P a` gets `C` to `P`, but `P`'s `Ord` lives only in
-- constraint sites, so `C` must re-inject it.
#guard (classSuperBinders
          [ { m3t5Sized with name := "C", supers := ["P"] },
            { m3t5Sized with name := "P", supers := ["Ord"] } ]).map (·.1)
         == ["C", "P"]
#guard ((classSuperBinders
          [ { m3t5Sized with name := "C", supers := ["P"] },
            { m3t5Sized with name := "P", supers := ["Ord"] } ]).find? (·.1 == "C")).map (·.2)
         == some ["[Ord {t}]", "[LT {t}]", "[LE {t}]", "[DecidableLT {t}]",
                  "[DecidableLE {t}]", "[Min {t}]", "[Max {t}]", "[BEq {t}]"]
-- DEDUP, first-occurrence order: `class (Eq a, Ord a) => C a` must not emit
-- `[BEq {t}]` twice (it is in `Ord`'s recipe as well).
#guard ((classSuperBinders [{ m3t5Sized with name := "C", supers := ["Eq", "Ord"] }]).head!).2
         == ["[BEq {t}]", "[Ord {t}]", "[LT {t}]", "[LE {t}]", "[DecidableLT {t}]",
             "[DecidableLE {t}]", "[Min {t}]", "[Max {t}]"]
-- An UNMAPPED builtin parent yields no binders and no entry (see `unmappedSupers`).
#guard classSuperBinders [{ m3t5Sized with name := "C", supers := ["Show"] }]
         == ([] : List (Name × List String))

/-! ### `stripClassConstraints` — the recipe at the constraint site

    `capOrdered :: Capped a => a -> a -> Bool`, as the shim delivers it. -/
def m3t5CapOrderedTy : GHCType :=
  .forAll "a" (.tyFun (.tyCon "Capped" [.tyVar "a"])
    (.tyFun (.tyVar "a") (.tyFun (.tyVar "a") (.tyCon "Bool" []))))

-- WITHOUT the recipes: `[Capped t]` alone — which is what the file looked like
-- before this task and cannot elaborate `decide (x < y)` (probe (c4)).
#guard (stripClassConstraints ["Capped"] m3t5CapOrderedTy).1 == ["[Capped a]"]
-- WITH them: the parent's binders FIRST, then the child's. This is the emitted
-- header of `capOrdered` in `Generated/SuperClass.lean`.
#guard (stripClassConstraints ["Capped"] m3t5CapOrderedTy (classSuperBinders [m3t5Capped])).1
         == ["[Ord a]", "[LT a]", "[LE a]", "[DecidableLT a]", "[DecidableLE a]",
             "[Min a]", "[Max a]", "[BEq a]", "[Capped a]"]
-- The STRIPPED TYPE is identical either way — the reason `emitBind`'s `resTyOf`
-- does not need the recipes and the header cannot drift from the result type.
#guard emitType (stripClassConstraints ["Capped"] m3t5CapOrderedTy).2
         == emitType (stripClassConstraints ["Capped"] m3t5CapOrderedTy
                        (classSuperBinders [m3t5Capped])).2
-- A recipe entry for a class NOT in this signature never fires, and a user class
-- with no entry is exactly as before.
#guard (stripClassConstraints ["Container"]
          (.forAll "a" (.tyFun (.tyCon "Container" [.tyVar "a"])
             (.tyFun (.tyVar "a") (.tyCon "Int" [])))) (classSuperBinders m3t5Plugin)).1
         == ["[Container a]"]

/-! ### Dropped superclasses are WARNED, never silent -/

#guard unmappedSupers ["Sized", "Container", "Capped"] m3t5Container == ([] : List Name)
-- A builtin WITH a recipe is not dropped (it reaches the constraint sites).
#guard unmappedSupers ["Capped"] m3t5Capped == ([] : List Name)
-- An unmapped builtin, an imported user class, and the plugin's placeholder for a
-- superclass predicate that is not a class constraint at all — all reported.
#guard unmappedSupers ["C"] { m3t5Sized with name := "C", supers := ["Show"] } == ["Show"]
#guard unmappedSupers ["C"] { m3t5Sized with name := "C", supers := ["Sized"] } == ["Sized"]
#guard unmappedSupers ["C"] { m3t5Sized with name := "C", supers := ["_UnknownSuper"] }
         == ["_UnknownSuper"]
#guard ((unmappedSuperWarning "C" "Show").splitOn
          "class `C` has the superclass `Show`, which is DROPPED").length == 2

/-! ### The dictionary attribution, on the observed spines

    Uniques are the extended fixture's (`/tmp/transpile-SuperClass.json`). -/
def m3t5CsizeV : Var :=
  {name := "$csize", unique := 10824, ty := .tyFun (.tyCon "Bag" []) (.tyCon "Int" []), role := .id}
def m3t5CemptyV : Var :=
  {name := "$cempty", unique := 10834, ty := .tyCon "Bag" [], role := .id}
def m3t5CinsertV : Var :=
  {name := "$cinsert", unique := 10839,
   ty := .tyFun (.tyCon "Int" []) (.tyFun (.tyCon "Bag" []) (.tyCon "Bag" [])), role := .id}
def m3t5SizedDictV : Var :=
  {name := "$fSizedBag", unique := 9900, ty := .tyCon "_Unknown" [], role := .dict}
def m3t5CsizeBind : Bind := .nonRec m3t5CsizeV (.lit (.litInt 0))
def m3t5CemptyBind : Bind := .nonRec m3t5CemptyV (.lit (.litInt 0))
def m3t5CinsertBind : Bind := .nonRec m3t5CinsertV (.lit (.litInt 0))
-- `$fSizedBag = $csize` — the newtype dictionary.
def m3t5SizedDfun : Bind :=
  .nonRec {name := "$fSizedBag", unique := 9900, ty := .tyCon "Sized" [.tyCon "Bag" []],
           role := .dict}
    (.var m3t5CsizeV)
-- `$fContainerBag = C:Container @Bag $fSizedBag $cempty $cinsert`.
def m3t5ContainerDfun : Bind :=
  .nonRec {name := "$fContainerBag", unique := 9904,
           ty := .tyCon "Container" [.tyCon "Bag" []], role := .dict}
    (.app (.app (.app (.app
      (.var {name := "C:Container", unique := 9950, ty := .tyCon "_Unknown" [], role := .id})
      (.type_ (.tyCon "Bag" [])))
      (.var m3t5SizedDictV))
      (.var m3t5CemptyV))
      (.var m3t5CinsertV))
def m3t5Binds : CoreProgram :=
  [m3t5CsizeBind, m3t5CemptyBind, m3t5CinsertBind, m3t5SizedDfun, m3t5ContainerDfun]
def m3t5SizedInst : Instance :=
  {className := "Sized", headTypes := [.tyCon "Bag" []], dfunName := "$fSizedBag",
   dfunUnique := 9900}
def m3t5ContainerInst : Instance :=
  {className := "Container", headTypes := [.tyCon "Bag" []], dfunName := "$fContainerBag",
   dfunUnique := 9904}

-- THE FIX, at its source: both methods attributed, superclass dict skipped.
#guard (dfunMethodBinds m3t5Binds m3t5Container m3t5ContainerInst).map (fun (m, v, _) => (m, v.unique))
         == [("empty", 10834), ("insert", 10839)]
-- The newtype-dictionary shape.
#guard (dfunMethodBinds m3t5Binds m3t5Sized m3t5SizedInst).map (fun (m, v, _) => (m, v.unique))
         == [("size", 10824)]
-- DECLINE ARMS, each returning `[]` (never a partial attribution):
-- name disagreement — the tripwire for a GHC field order that stops matching
-- `classOpItems` order,
#guard (dfunMethodBinds m3t5Binds
          { m3t5Container with methods := m3t5Container.methods.reverse }
          m3t5ContainerInst).isEmpty
-- arity disagreement (the class channel lists a method the dictionary lacks),
#guard (dfunMethodBinds m3t5Binds
          { m3t5Container with methods := m3t5Container.methods.take 1 }
          m3t5ContainerInst).isEmpty
-- no dfun bind at all (an instance whose dict-builder was filtered),
#guard (dfunMethodBinds [m3t5CsizeBind] m3t5Sized m3t5SizedInst).isEmpty
-- and a `$c` Var the binds do not contain (the ref would dangle, so it is not
-- claimed as an attribution).
#guard (dfunMethodBinds [m3t5SizedDfun] m3t5Sized m3t5SizedInst).isEmpty

-- THE OLD MATCHER'S VERDICT on the same two methods, for contrast: `[]` spine ⇒
-- both unresolved ⇒ the whole instance dropped, which is Task 1's observation 4.
#guard classifyInstanceMethod [] m3t5Binds "Container" (emitType (.tyCon "Bag" []))
         (m3t5Container.methods.head!) == .unresolved
#guard classifyInstanceMethod [] m3t5Binds "Container" (emitType (.tyCon "Bag" []))
         (m3t5Container.methods.getLast!) == .unresolved
-- …and WITH the dictionary attribution, both are fields.
#guard classifyInstanceMethod [] m3t5Binds "Container" (emitType (.tyCon "Bag" []))
         (m3t5Container.methods.head!)
         (dfunMethodBinds m3t5Binds m3t5Container m3t5ContainerInst)
         == .field "_dollar_cempty_10834"
#guard classifyInstanceMethod [] m3t5Binds "Container" (emitType (.tyCon "Bag" []))
         (m3t5Container.methods.getLast!)
         (dfunMethodBinds m3t5Binds m3t5Container m3t5ContainerInst)
         == .field "_dollar_cinsert_10839"
-- End to end: the instance that used to vanish.
#guard emitInstanceUser [] [m3t5Sized, m3t5Container] m3t5Binds m3t5ContainerInst
         == some ("instance : Container (GHCCore.tyConOpaque \"Bag\") where\n" ++
                 "  empty := _dollar_cempty_10834\n  insert := _dollar_cinsert_10839")
-- …and it is no longer reported as dropped.
#guard unresolvedInstanceMethods
         { binds := m3t5Binds, typeDecls := [], instances := [m3t5SizedInst, m3t5ContainerInst],
           classDecls := [m3t5Sized, m3t5Container] }
         == ([] : List (Name × String × Name))

/-! ### `sortInstances` — parent instance before child instance

    MEASURED, not argued. `examples/haskell/SuperClass.hs` declares `instance
    Container Bag` ABOVE `instance Sized Bag` on purpose; the instance channel is
    in source order (`[Ord, Eq, Capped, Container, Sized]` for that file), and
    with the child emitted first Lean answered

        error: …/SuperClass.lean:75:25: Fields missing: `size`

    — the flattened form of probe (a)'s negative control. Re-run with the two
    source blocks swapped, the emitted `instance` order is the same either way
    (parent first) and only the `$csize` def moves, which is order-irrelevant. -/

#guard (sortInstances [m3t5Sized, m3t5Container] [m3t5ContainerInst, m3t5SizedInst]).map (·.className)
         == ["Sized", "Container"]
-- Already-correct input unchanged (the stability every other fixture relies on).
#guard (sortInstances [m3t5Sized, m3t5Container] [m3t5SizedInst, m3t5ContainerInst]).map (·.className)
         == ["Sized", "Container"]
-- Builtin instances are not dependencies and are not reordered around: `Capped`'s
-- parent is `Ord`, which contributes no `extends` and hence no ordering need.
#guard (sortInstances [m3t5Capped]
          [ {className := "Capped", headTypes := [.tyCon "Level" []],
             dfunName := "$fCappedLevel", dfunUnique := 10541},
            {className := "Ord", headTypes := [.tyCon "Level" []],
             dfunName := "$fOrdLevel", dfunUnique := 10555} ]).map (·.className)
         == ["Capped", "Ord"]
-- A DIFFERENT head is not a dependency: `Container Bag` does not wait for
-- `Sized Box`. (Order preserved, so the child still comes first — and Lean's
-- `Fields missing` is then the correct diagnosis, not something to sort away.)
#guard (sortInstances [m3t5Sized, m3t5Container]
          [ m3t5ContainerInst,
            {className := "Sized", headTypes := [.tyCon "Box" []], dfunName := "$fSizedBox",
             dfunUnique := 1} ]).map (·.className)
         == ["Container", "Sized"]
-- No user classes at all ⇒ identity, which is why the 26 non-class fixtures are
-- byte-identical.
#guard (sortInstances [] [m3t5ContainerInst, m3t5SizedInst]).map (·.className)
         == ["Container", "Sized"]

/-! ### Regression — what this task could have moved, and what it did

    Every new parameter is TRAILING with a `[]` default (`emitClassDecl`'s
    `classNames`, `stripClassConstraints`' `superBinders` and its threading through
    `emitDefHeader`/`emitBind`/`emitProgram`/`emitProgramWith`,
    `classifyInstanceMethod`'s `spine`), so every pre-existing call site — this
    file's `#guard`s included — keeps its exact meaning. The two exceptions are
    mechanical: `stripClassConstraintsGo` gained a positional second argument
    (`[]` at both call sites here), and `dfunMethodBinds` is consulted before the
    old matcher wherever an instance is emitted.

    The three ORDER changes are the real risk, and all three are stable on input
    that needs no reordering: `sortClassDecls`, `sortInstances`, and the
    `extends` clause itself (empty unless a super names a LOCAL class).

    MEASURED, in two passes. The task's own pass compared against the on-disk
    pre-change `Generated/` files (untracked — `Generated/` is gitignored), which
    assumes those snapshots were current rather than re-deriving them; that
    assumption proved false for at least `BothNotations.lean` (stale since it
    predates the `import GhcCoreToLean.Runtime` header change). The REVIEW then
    redid it the Task 4 way — parent binary stashed, both binaries run over the
    same dumps — and found **29 fixtures byte-identical**, `SuperClass.lean`
    alone excepted, which is this task's deliverable. The three multi-module
    fixtures (`OperatorCommons`, `RatioFalseTest`, `RecordClient`) need
    `LEAN_IMPORTS` plus the manifest's newtype channel supplied, or they diff for
    harness reasons rather than drift.
    Includes every class fixture (`UserClass`, `DefaultMethods`,
    `OperatorShadow`, `TwoClassesDistinctMethods`, `UserClassNeq`,
    `BuiltinConstraints`, `Ratio`, `RecordOps`, `NewtypeBasic`, `OrdInstance`,
    `NumOrd`). Byte-identity is also what settles the fixtures whose `lake build`
    is RED — `UserClass` (a `blaster ❌ Falsified` at its one theorem),
    `TupleTriple`, `BothNotations`, `RatioCeilTruncate`, `RatioComparisons`, and
    `RatioFalseTest` (intentionally false): an identical emitted file has an
    identical build result, so every one of those reds predates this task (the
    plan's Task 8 notes already carry `UserClass` as known-red).
    The three refusal fixtures still refuse with their own messages
    (`NewtypeInstances` — newtype instance head; `UserClassNeqWithEq` — the `/=`
    method; `TwoClassesSameMethod` — still rejected by GHC itself, before the
    transpiler runs).

    `SuperClass.lean`'s own delta, relative to the DEGRADED file Task 1 recorded:
    `class Container … extends Sized a`, an emitted `instance : Container Bag`
    with both fields, the parent instance sorted ahead of it, and the new
    builtin-super half (`class Capped`, `instance : Capped Level`, and the
    `[Ord t] … [Capped t]` headers on `capBoth`/`capOrdered`). Its seven
    properties verify: two `blaster` `✅ Valid`, five ground `decide`/`rfl`.
    stderr is EMPTY — the `Container Bag` drop warning M3 Task 4 added is gone
    because the drop is gone. -/

/-! ## M3 Task 6 — hand-written non-structural `Ord`

    The defect this closes is the oldest silent-wrong in the emitter: `ordTypes` was
    INSTANCE-EXISTENCE-based, so ANY type with an `Ord` instance got `deriving Ord`
    and its real `$ccompare`/`$c<`/… bodies were dropped by `isSuppressedMethod`. A
    hand-written non-structural `Ord` was therefore replaced by Lean's structural
    order, silently. `Emit.ordRoute` decides per instance now; its section header
    carries the design, and this block carries the measurements.

### The A/B, quoted

    `examples/haskell/OrdHandwritten.hs`, one dump (`/tmp/transpile-OrdHandwritten.
    json`), two binaries — the parent binary built by stashing `Emit.lean`/`Main.lean`,
    the way M3 Task 4's regression pass did. PRE-fix, `decide` does not merely fail
    to prove the Haskell truths, it PROVES THEM FALSE:

        error: …/OrdHandwritten.lean:209:71: Tactic `decide` proved that the proposition
          revLt (Rev.Rev 1) (Rev.Rev 2) = false
        is false
        error: …/OrdHandwritten.lean:233:70: Tactic `decide` proved that the proposition
          fracMin (Frac.Frac 1 2) (Frac.Frac 2 5) = Frac.Frac 2 5
        is false
        error: …/OrdHandwritten.lean:236:66: Tactic `decide` proved that the proposition
          fracOrdered (Frac.Frac 1 2) (Frac.Frac 2 5) = false
        is false

    …and `blaster` refutes the quantified ones with counterexamples:

        error: …/OrdHandwritten.lean:217:76: ❌ Falsified
        error: …/OrdHandwritten.lean:217:76: Counterexample:
        error: …/OrdHandwritten.lean:217:76: - a: 0
        error: …/OrdHandwritten.lean:217:76: - b: (- 1)

    Counted: of the fixture's 20 properties, PRE-fix 11 are `decide`-refuted
    (`revLt`×2, `revCompare`, `revMin`, `fracLt`×2, `fracMin`, `fracOrdered`×2,
    `fracCap`×2) and 2 are `blaster`-falsified with counterexamples
    (`revLt_reverses_all`, `fracLt_all`) — 13 refuted, 7 passing (the `Rank`,
    `Pair`, `fracEq` and `minDefEq` ones, none of which discriminates). POST-fix all
    20 hold: 2 `blaster` `✅ Valid`, 18 ground `decide`, and
    `lake build GhcCoreToLean.Generated.OrdHandwritten` reports 0 errors.

    THE TWO SILENT-WRONGS SEPARATELY, since they are different defects:

    * MONOMORPHIC (`revLt`, `fracLt`) — pre-existing, predates M3. The emitted
      `wLt`-style body is `decide (a < b)` against `deriving Ord`.
    * `Ord`-CONSTRAINED (`fracMin` via `minOf :: Ord a => …`, and `fracOrdered` via
      `cappedOrdered :: Capped a => …` where `class Ord a => Capped a`) — this is the
      loud→silent REGRESSION M3 Task 5 introduced. Before Task 5 a builtin-superclass
      constraint site got no binder recipe, so `decide (x < y)` there could not
      elaborate at all (`failed to synthesize LT t`); Task 5 supplied `[Ord t] [LT t]
      … [BEq t]` and every binder then resolved — against the structural order. The
      pre-fix refutation of `fracOrdered_viaCapped` above IS that regression:
      elaborated, and wrong. Closing the root cause closes it, which is this task's
      acceptance criterion.

    The pre-fix file also shows the drop in the negative: ZERO `$ccompare` defs
    emitted for five `Ord` instances, and `inductive MinDef … deriving Repr,
    Inhabited, DecidableEq, Ord` for a type whose hand-written `(<=)` is the REVERSE
    of that structural order, with no warning on stderr.

### What is derived, measured — the boundary is not where the plan assumed

    Six shapes in one module (`OrdBoundary`, scratch), asking only whether GHC's
    `$ccompare` body contains `dataToTag#`/`tagToEnum#`:

        data E2 = A2 | B2                              tagprim=False  → handwritten
        data E3 = A3 | B3 | C3                         tagprim=True   → derived
        data E4 = A4 | B4 | C4 | D4                    tagprim=True   → derived
        data Q2 = Q2a Int | Q2b Int                    tagprim=False  → handwritten
        data Q3 = Q3a Int | Q3b Int | Q3c Int          tagprim=False  → handwritten
        data S1 = S1 Int Int                           tagprim=False  → handwritten

    (all `deriving (Eq, Ord)`). So the DERIVED route is now reached ONLY by an
    all-nullary enum with ≥3 constructors; everything else — including
    `OrdInstance.hs`'s `data Coin = Heads | Tails deriving (Eq, Ord)` — takes the
    hand-written route with GHC's own derived body. The plan's byte-identity
    expectation ("OrdInstance … should stay derived/identical") is therefore WRONG,
    and `Generated/OrdInstance.lean` legitimately changed: `deriving …, Ord` +
    four companions became a `$ccompare` def + `instance : Ord Coin` + the same four
    companions. It builds clean and `pick` still computes `Heads ≤ Tails`.

### `M3T6B` — the misclassification is SOUND, exhaustively

    Direction (b) (derived read as hand-written) is sound because the derived
    `compare` body IS the derived order. Measured, not argued: the three bodies below
    are verbatim transpiler output for the three shapes above, checked against Lean's
    own `deriving Ord` on the same inductive over the whole constructor space with
    fields sampled to hit `<`, `=` and `>`. -/

inductive M3T6BE2 where | A2 : M3T6BE2 | B2 : M3T6BE2
deriving Repr, Inhabited, DecidableEq, Ord
inductive M3T6BQ3 where
  | Q3a : Int → M3T6BQ3 | Q3b : Int → M3T6BQ3 | Q3c : Int → M3T6BQ3
deriving Repr, Inhabited, DecidableEq, Ord
inductive M3T6BS1 where | S1 : Int → Int → M3T6BS1
deriving Repr, Inhabited, DecidableEq, Ord

def m3t6e2cmp (a b : M3T6BE2) : Ordering :=
  (match a with
| M3T6BE2.A2 => (match b with
| M3T6BE2.A2 => Ordering.eq
| _ => Ordering.lt)
| M3T6BE2.B2 => (match b with
| M3T6BE2.B2 => Ordering.eq
| _ => Ordering.gt))

def m3t6q3cmp (a b : M3T6BQ3) : Ordering :=
  (match a with
| M3T6BQ3.Q3a a1 => (match b with
| M3T6BQ3.Q3a b1 => ((compare) (a1)) (b1)
| _ => Ordering.lt)
| M3T6BQ3.Q3b a1 => (match b with
| M3T6BQ3.Q3a _ => Ordering.gt
| M3T6BQ3.Q3b b1 => ((compare) (a1)) (b1)
| _ => Ordering.lt)
| M3T6BQ3.Q3c a1 => (match b with
| M3T6BQ3.Q3c b1 => ((compare) (a1)) (b1)
| _ => Ordering.gt))

def m3t6s1cmp (a b : M3T6BS1) : Ordering :=
  (match a with
| M3T6BS1.S1 a1 a2 => (match b with
| M3T6BS1.S1 b1 b2 => (match ((compare) (a1)) (b1) with
| Ordering.lt => Ordering.lt
| Ordering.eq => ((compare) (a2)) (b2)
| Ordering.gt => Ordering.gt)))

def m3t6e2s : List M3T6BE2 := [.A2, .B2]
def m3t6q3s : List M3T6BQ3 :=
  ([-1, 0, 1] : List Int).flatMap fun i => [.Q3a i, .Q3b i, .Q3c i]
def m3t6s1s : List M3T6BS1 :=
  ([-1, 0, 1] : List Int).flatMap fun i => ([-1, 0, 1] : List Int).map fun j => .S1 i j

#guard m3t6e2s.all fun a => m3t6e2s.all fun b => compare a b == m3t6e2cmp a b
#guard m3t6q3s.all fun a => m3t6q3s.all fun b => compare a b == m3t6q3cmp a b
#guard m3t6s1s.all fun a => m3t6s1s.all fun b => compare a b == m3t6s1cmp a b
-- …and the samples really do exercise all three answers, so the agreement above is
-- not the vacuous "both always say `eq`".
#guard (m3t6q3s.flatMap fun a => m3t6q3s.map fun b => m3t6q3cmp a b).eraseDups.length == 3
#guard (m3t6s1s.flatMap fun a => m3t6s1s.map fun b => m3t6s1cmp a b).eraseDups.length == 3

/-! ### Direction (a) — hand-written read as DERIVED: the residual, measured

    This is the silent-wrong direction, and it is closed for every body GHC
    generates from ordinary Haskell. Probed adversarially rather than asserted:

    * `compare a b = compare (fromEnum b) (fromEnum a)` on a `deriving Enum` type —
      `$ccompare` `tagprim=False` (the primop stays inside `$cfromEnum`; nothing
      inlines at `-O0`), so it is correctly read as hand-written.
    * `{-# LANGUAGE MagicHash #-}` + `compare a b = compare (I# (dataToTag# b))
      (I# (dataToTag# a))` — `$ccompare` `tagprim=True`. THAT ONE IS STILL
      SILENT-WRONG: the reversed order is replaced by the structural one. Confirmed
      by the byte-identity sweep, where that module (`OrdAdv`) is IDENTICAL under
      both binaries.

    Kept as a pinned residual rather than closed, for two reasons. Closing it needs
    instance ORIGIN, which only the decl-plugin can supply (the same extension M2
    named for `deriving` on a newtype); and the alternative available here — a shape
    test on GHC's derived-`compare` code — is fragile in the wrong direction: a false
    negative would make every genuinely derived `Ord` loud. It is also no worse than
    the pre-task state, where every hand-written `Ord` was silently structural.

### `ordRoute`, `emitDataDecl`, `emitInstance` — the three routes as guards -/

def m3t6RevTy  : GHCType := .tyCon "Rev" []
def m3t6RevHd  : String  := emitType m3t6RevTy
def m3t6CmpVar : Var :=
  { name := "$ccompare", unique := 11235,
    ty := .tyFun m3t6RevTy (.tyFun m3t6RevTy (.tyCon "Ordering" [])), role := .id }
-- A body with no tag primop: the user's own `compare`, whatever it computes.
def m3t6Plain : Expr :=
  .var { name := "GHC.Classes.compare", unique := 0, ty := .tyCon "_Unknown" [], role := .id }
-- A body with one: GHC's derived `compare` on a ≥3-constructor enum.
def m3t6TagPrim : Expr :=
  .app (.var { name := "GHC.Prim.dataToTag#", unique := 0,
               ty := .tyCon "_Unknown" [], role := .id }) m3t6Plain
def m3t6Dfun : Var :=
  { name := "$fOrdRev", unique := 3350, ty := .tyCon "_Unknown" [], role := .dict }
def m3t6OrdInst : Instance :=
  { className := "Ord", headTypes := [m3t6RevTy], dfunName := "$fOrdRev", dfunUnique := 3350 }

-- HAND-WRITTEN: a standalone `$ccompare` with no primop, carrying the def name the
-- emitted instance must point at.
#guard ordRoute [.nonRec m3t6CmpVar m3t6Plain] m3t6RevHd == .handwritten "_dollar_ccompare_11235"
-- DERIVED: tag primop ⇒ the data-block route, exactly as before this task.
#guard ordRoute [.nonRec m3t6CmpVar m3t6TagPrim] m3t6RevHd == .derived
-- UNSUPPORTED: `$ccompare` sharing a Rec group with the instance's own dict builder
-- is GHC's class default (the `<=`-only minimal definition), not the user's body.
#guard ordRoute [.rec_ [(m3t6Dfun, m3t6Plain), (m3t6CmpVar, m3t6Plain)]] m3t6RevHd == .unsupported
-- …and the group's ORDER is irrelevant (the dfun came second in the real dump for
-- some instances and first for others).
#guard ordRoute [.rec_ [(m3t6CmpVar, m3t6Plain), (m3t6Dfun, m3t6Plain)]] m3t6RevHd == .unsupported
-- A Rec group with no dict builder is still the user's own body: the test is
-- membership of a `$f…`, never the group's head or its size.
#guard ordRoute [.rec_ [(m3t6CmpVar, m3t6Plain)]] m3t6RevHd == .handwritten "_dollar_ccompare_11235"
-- No `$ccompare` at all, and a `$ccompare` at ANOTHER head, both decline.
#guard ordRoute [] m3t6RevHd == .unsupported
#guard ordRoute [.nonRec m3t6CmpVar m3t6Plain] (emitType (.tyCon "Other" [])) == .unsupported

-- The companion block, character-exact and in ONE place: `emitDataDecl` (derived)
-- and `emitInstance` (hand-written) must not drift apart, since the whole coherence
-- argument is that `<`/`≤`/`min`/`max` are functions of `compare` on both routes.
#guard ordCompanionInsts "Rev" ==
  "instance : LE Rev := leOfOrd\ninstance : LT Rev := ltOfOrd\n" ++
  "instance : Min Rev := minOfLe\ninstance : Max Rev := maxOfLe"

#guard emitInstance [] [] [] [.nonRec m3t6CmpVar m3t6Plain] m3t6OrdInst ==
  some (s!"instance : Ord {m3t6RevHd} where\n  compare := _dollar_ccompare_11235\n\n"
          ++ ordCompanionInsts m3t6RevHd)
-- Derived and unsupported both emit nothing HERE (the data block, resp. nothing).
#guard emitInstance [] [] [] [.nonRec m3t6CmpVar m3t6TagPrim] m3t6OrdInst == none
#guard emitInstance [] [] [] [.rec_ [(m3t6Dfun, m3t6Plain), (m3t6CmpVar, m3t6Plain)]]
         m3t6OrdInst == none

def m3t6RevDecl : DataDecl :=
  { name := "Rev", kind := "data",
    ctors := [{ name := "Rev", fields := [{ name := "_", ty := .tyCon "Int" [] }] }] }
-- Task 3's mandatory handoff: a hand-written-`Ord` type still gets `DecidableEq`
-- (so `[BEq t]` in the `Ord` recipe is synthesizable) but NOT `Ord` and NOT the
-- companions — those come with the instance.
#guard emitDataDecl false false m3t6RevDecl (handwrittenOrd := true) ==
  "inductive Rev where\n  | Rev : Int → Rev\nderiving Repr, Inhabited, DecidableEq"
-- The derived route is unchanged, and the new parameter is trailing+defaulted so
-- every pre-existing call site (the `emitDataDecl` guards at the top of this file
-- included) keeps its exact meaning.
#guard emitDataDecl false true m3t6RevDecl ==
  "inductive Rev where\n  | Rev : Int → Rev\nderiving Repr, Inhabited, DecidableEq, Ord\n\n"
    ++ ordCompanionInsts "Rev"

-- The diagnostic, and its scope: only the unsupported route is reported.
#guard unsupportedOrdInstances
         { binds := [.rec_ [(m3t6Dfun, m3t6Plain), (m3t6CmpVar, m3t6Plain)]],
           typeDecls := [m3t6RevDecl], instances := [m3t6OrdInst] } == ["Rev"]
#guard unsupportedOrdInstances
         { binds := [.nonRec m3t6CmpVar m3t6Plain], typeDecls := [m3t6RevDecl],
           instances := [m3t6OrdInst] } == []
#guard unsupportedOrdInstances
         { binds := [.nonRec m3t6CmpVar m3t6TagPrim], typeDecls := [m3t6RevDecl],
           instances := [m3t6OrdInst] } == []

/-! ### Whole-program: which `$c` binds survive, and where the instance lands

    The suppression is the other half of the fix — a hand-written head keeps exactly
    ONE `$c` bind (`$ccompare`), and the derived head keeps none. Checked through
    `emitFullProgram` so the section ORDER is checked with it: the `$ccompare` def
    must precede the `instance : Ord`, which must precede the companions.

    THE SECTION EXISTS BECAUSE TWO DESIGNS FAILED FIRST, both measured. Putting the
    `$ccompare` def in the ordinary method-def section and the instance in the
    instance section (the plan's reading of "mind the forward-visibility ordering")
    is wrong in two ways at once:

    * NESTED derived-`Ord` types. `data A = A Int deriving (Eq, Ord); data B = B A
      deriving (Eq, Ord)` — both `.handwritten`, and B's compare body is
      `compare a1 b1` AT TYPE `A`:

          error: …/OrdNested.lean:58:19: failed to synthesize
            Ord A

      A REGRESSION on ordinary Haskell (pre-task both got data-block `deriving Ord`
      in `sortDataDecls` order), and one no corpus fixture exhibits — the 30/4
      byte-identity sweep could not have caught it.
    * ANOTHER class's `$c` method using an order operator at such a head.
      `instance Capped Frac where cap x y = min x y` in `OrdHandwritten.hs`:

          error: …/OrdHandwritten.lean:144:4: failed to synthesize
            Min Frac

      (plus two downstream `decide` failures where the `sorry`-ed def blocked
      reduction). This was first written up as an unfixable residual and it is not
      one: it disappears for the same reason the nested case does.

    Both are fixed by giving hand-written `Ord` its OWN section — per type,
    `$ccompare` def then `instance : Ord T` then the companions — placed first in
    `bodyRaw`, ordered by the emitted DATA order. It stays in `bodyRaw` rather than
    joining the data block because the compare body pattern-matches constructors and
    needs `resolveUserCtors`, which must never see the data block. Re-measured after
    the move: `OrdNested` elaborates clean, `OrdHandwritten` is 0 errors/20
    properties, and the 30 byte-identical fixtures did not move (a module with no
    hand-written `Ord` gets an EMPTY `ordStr`, which `List.filter (· != "")` drops,
    so `bodyRaw` is character-for-character what it was). -/

def m3t6HandwrittenProg : Program :=
  { binds := [.nonRec m3t6CmpVar m3t6Plain], typeDecls := [m3t6RevDecl],
    instances := [m3t6OrdInst] }
def m3t6DerivedProg : Program :=
  { binds := [.nonRec m3t6CmpVar m3t6TagPrim], typeDecls := [m3t6RevDecl],
    instances := [m3t6OrdInst] }

#guard ((emitFullProgram [] m3t6HandwrittenProg).splitOn "def _dollar_ccompare_11235").length == 2
#guard ((emitFullProgram [] m3t6HandwrittenProg).splitOn "instance : Ord Rev where").length == 2
#guard ((emitFullProgram [] m3t6HandwrittenProg).splitOn
         "deriving Repr, Inhabited, DecidableEq\n").length == 2
-- Order: compare def, then the instance, then its companions.
#guard ((emitFullProgram [] m3t6HandwrittenProg).splitOn "def _dollar_ccompare_11235").length == 2
  && (((emitFullProgram [] m3t6HandwrittenProg).splitOn "def _dollar_ccompare_11235")[1]!.splitOn
        "instance : Ord Rev where").length == 2
  && ((((emitFullProgram [] m3t6HandwrittenProg).splitOn "instance : Ord Rev where")[1]!.splitOn
        "instance : LE Rev := leOfOrd").length == 2)
-- DERIVED: no method def at all, `Ord` on the inductive, companions in the data
-- block — byte-for-byte the pre-task treatment.
#guard ((emitFullProgram [] m3t6DerivedProg).splitOn "_dollar_ccompare").length == 1
#guard ((emitFullProgram [] m3t6DerivedProg).splitOn
         "deriving Repr, Inhabited, DecidableEq, Ord").length == 2
#guard ((emitFullProgram [] m3t6DerivedProg).splitOn "instance : Ord Rev where").length == 1

/-! ### `M3T6R` — TWO `BEq` routes, one answer, in the NEW section order

    M3 Task 3 measured this for a type whose `Ord` came from `deriving`; Task 6 makes
    the `Ord` an instance BLOCK, which is a different elaboration order, and the
    hazard is unchanged: a hand-written cross-multiply `Eq` (emitted `instance : BEq
    T`) alongside the `deriving DecidableEq` that Task 6 emits for a hand-written-Ord
    type gives core's `instBEqOfDecidableEq` a second candidate. If the structural
    one won, every `Eq`-constrained call at that type would silently report
    structural equality.

    It does not win: `#synth BEq` answers the local instance. Note what did NOT
    change — `fracEq_crossMultiplies` in the fixture holds under BOTH binaries, so
    it is a no-regression check, not a discriminator. What changed is the REASON the
    `DecidableEq` route exists (`deriving Ord` before, Task 6's explicit flag now),
    which is why the selection is re-pinned here rather than assumed to carry over. -/

inductive M3T6R where
  | mk : Int → Int → M3T6R
deriving Repr, Inhabited, DecidableEq

def m3t6RCmp : M3T6R → M3T6R → Ordering := fun a b => match a, b with
  | .mk p q, .mk r s => compare (p * s) (r * q)
def m3t6REq : M3T6R → M3T6R → Bool := fun a b => match a, b with
  | .mk p q, .mk r s => p * s == r * q

-- The emitter's own order: data + `deriving`, then the `$c` defs, then the
-- instances (`Ord` first, then its companions).
instance : Ord M3T6R where compare := m3t6RCmp
instance : LE M3T6R := leOfOrd
instance : LT M3T6R := ltOfOrd
instance : Min M3T6R := minOfLe
instance : Max M3T6R := maxOfLe
instance : BEq M3T6R where beq := m3t6REq

-- The full `Ord`-constraint recipe (M3 Task 3), at a head whose `Ord` is an
-- instance block: every binder still resolves — `DecidableLT`/`DecidableLE` come
-- from core's `DecidableRel (@LT.lt α ltOfOrd)` matching `ltOfOrd` literally, which
-- is why the companions must be spelled that way and not inlined.
def m3t6OrdAt {t : Type} [Ord t] [LT t] [LE t] [DecidableLT t] [DecidableLE t]
    [Min t] [Max t] [BEq t] (x y : t) : Bool := (x == y) || decide (x < y)

-- 1/2 == 2/4 under cross-multiply (structural: false) — the hand-written `BEq` wins.
#guard ((M3T6R.mk 1 2) == (M3T6R.mk 2 4)) == true
#guard m3t6OrdAt (M3T6R.mk 1 2) (M3T6R.mk 2 4) == true
-- 1/2 > 1/3 under cross-multiply (structural: `1 = 1`, then `2 < 3` ⇒ LT) — the
-- hand-written ORDER wins, through the constrained call.
#guard m3t6OrdAt (M3T6R.mk 1 2) (M3T6R.mk 1 3) == false
#guard m3t6OrdAt (M3T6R.mk 1 3) (M3T6R.mk 1 2) == true
-- The companions follow `compare`, so `min` disagrees with the structural one too.
#guard (min (M3T6R.mk 1 2) (M3T6R.mk 1 3)) == M3T6R.mk 1 3

/-! ### `dfunDumpUnique` — the two channels do not number uniques the same way

    The reviewer's hardening nit ("`findBind` at the dfun lookup resolves by NAME
    only, ignoring `i.dfunUnique` that's right there") turned out NOT to be a
    no-op: matching the two raw resolved NOTHING, and `SuperClass.hs`'s
    `instance : Container Bag` disappeared from the emitted output — the one
    non-Ord diff in the whole byte-identity sweep, which is how it was caught.

    The instance channel's unique is the decl plugin's `getKey (nameUnique …)`,
    GHC's packed 64-bit key `(tag << 56) ||| index`; a bind's unique is the shim's
    `BinderId (Unique _ n) → n`, the index alone. `$fOrdLevel` in
    `/tmp/transpile-SuperClass.json` is the whole discovery in one pair of numbers.
    Verified across all 40 dumps in `/tmp/transpile-*.json`: 60/60 instances match
    after masking, 0 mismatches, high byte always `114` (`'r'`); and 0 dumps contain
    two top-level binds sharing a dfun name, which is why this is hardening. The
    caller falls back to the name-only lookup when the keyed one misses, so a future
    renumbering degrades to today's behaviour instead of dropping every instance. -/

#guard dfunDumpUnique 8214565720323795259 == 10555
-- Already-in-dump-space values (what this file's own `Instance` literals use, and
-- what the fallback path would see) pass through unchanged.
#guard dfunDumpUnique 9904 == 9904
#guard dfunDumpUnique 0 == 0

/-! ### Regression — what this task could have moved, and what it did

    BYTE-IDENTITY, by the Task 4/reviewer method (parent binary stashed and saved,
    both binaries run over the SAME dumps with the SAME environment) — NOT against
    on-disk `Generated/` snapshots, which M3 Task 5's review proved stale for at
    least one file. Final pass: whole corpus re-transpiled first so every dump is
    current, 36 dumps in `/tmp/transpile-*.json`:

    * **30 IDENTICAL** (stdout AND stderr): `Arithmetic`, `BothNotations`,
      `BuiltinConstraints`, `CaseBinder`, `DefaultMethods`, `Fib`, `FibComplex`,
      `ListBasics`, `ListLibrary`, `ListLiterals`, `LocalRec`, `NewtypeBasic`,
      `NumOrd`, `OperatorCommons`, `OperatorShadow`, `OrdAdv`, `PartialHead`,
      `PreludeNames`, `Ratio`, `RatioCeilTruncate`, `RatioComparisons`,
      `RatioFalseTest`, `RecordClient`, `RecordOps`, `SuperClass`, `TupleBasics`,
      `TupleTriple`, `TwoClassesDistinctMethods`, `UserClass`, `UserClassNeq`.
      `SuperClass` is identical only after the `dfunDumpUnique` fix — see that block.
      `NumOrd` and `Ratio` are the two that would have moved had the `Ord` change
      over-fired: `NumOrd` uses the `Ord` operators monomorphically at `Int` (no
      instance to route), and `Ratio`'s `CustomRatio`/`CustomRatioSOP` have
      hand-written `Eq` and NO `Ord` at all. `OrdAdv` is direction (a)'s residual —
      identical BECAUSE the misclassification is still there.
    * **4 legitimately DIFFERENT**, every one an `Ord`-route change and nothing else
      (diffed line-kind by line-kind): `deriving …, Ord` dropped, a `$ccompare` def
      added, `instance : Ord T` + the four companions added. `OrdInstance` (`Coin`,
      the 2-ctor enum flip — see the boundary block) is the only CORPUS fixture among
      them; `OrdHandwritten` is this task's new fixture, `OrdProbe`/`OrdBoundary` its
      scratch probes. An earlier pass over a wider set of then-present dumps (before
      /tmp was purged of them) added `PairProbe` and `ShowSuperProbe` to the
      IDENTICAL column and `DefaultUnderOrd`, `OrdHwCapped`, `OrdHwDirect` (the
      reviewer's hand-written-`Ord` probes) to this one.
    * **2 REFUSALS intact**, same exit code, no file written, byte-identical stderr
      under both binaries: `NewtypeInstances` (newtype instance head) and
      `UserClassNeqWithEq` (Task 2's builtin-method collision). `TwoClassesSameMethod`
      is still rejected by GHC itself, before the transpiler runs.

    `lake build GhcCoreToLean.Generated.<M>` green (0 errors) after the change on 25
    modules, the whole corpus re-transpiled with the final binary first:
    `OrdHandwritten`, `OrdInstance`, `SuperClass`, `BuiltinConstraints`,
    `DefaultMethods`, `Ratio`, `RecordOps`, `NewtypeBasic`, `ListLibrary`,
    `TupleBasics`, `Arithmetic`, `NumOrd`, `PartialHead`, `UserClassNeq`,
    `TwoClassesDistinctMethods`, `OperatorShadow`, `PreludeNames`, `CaseBinder`,
    `ListBasics`, `ListLiterals`, `LocalRec`, `Fib`, `FibComplex`, `RecordClient`,
    `OperatorCommons`. Plus the off-corpus `OrdNested` probe (`lake env lean`, clean
    — it is the nested case the section fix exists for). The remaining
    known-red fixtures (`UserClass`'s falsified theorem, `TupleTriple`,
    `BothNotations`, `RatioCeilTruncate`, `RatioComparisons`, `RatioFalseTest`) are
    byte-identical, so an identical emitted file has an identical build result and
    every one of those reds predates this task.

    ONE stderr line is NEW, and only for the new fixture: `OrdHandwritten.hs`'s
    `Ord MinDef` warning (`unsupportedOrdInstances`). No corpus module has a
    `<=`-only instance, so no other fixture's stderr moved. -/

end GhcCoreToLean.Tests
