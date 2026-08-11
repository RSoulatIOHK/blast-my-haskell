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
#guard (emitInstance [] [] eqInstProgram eqInst).isSome
#guard (((emitInstance [] [] eqInstProgram eqInst).getD "").splitOn "instance : BEq (GHCCore.tyConOpaque \"Foo\")").length == 2

-- Tier 3 Task 2/4: Ord is reconstructed via `deriving Ord` + LE/LT/Min/Max in
-- the data block (instances precede binds; Lean instances aren't forward-
-- visible), so `emitInstance` emits nothing for Ord — it's covered by the
-- emitDataDecl guards below.
def ordInst : Instance :=
  {className := "Ord", headTypes := [.tyCon "Foo" []], dfunName := "$fOrdFoo", dfunUnique := 98}
#guard emitInstance [] [] [] ordInst == none

-- Tier 3 Task 3: Show instances are intentionally skipped (derived Repr handles printing).
def showInst : Instance :=
  {className := "Show", headTypes := [.tyCon "Foo" []], dfunName := "$fShowFoo", dfunUnique := 97}
#guard emitInstance [] [] [] showInst == none

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
#guard emitInstance [] ["(GHCCore.tyConOpaque \"Foo\")"] eqInstProgram eqInst == none
#guard (emitInstance [] [] eqInstProgram eqInst).isSome

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
#guard emitClassDecl sizedClass == "class Sized (a : Type) where\n  size : (a → Int)"

-- Dict Task 4: a bare class-method selector emits `Class.method`; others unaffected.
#guard emitVar [{ method := "size", cls := "Sized" }] [] {name := "size", unique := 7, ty := .tyFun (.tyVar "a") (.tyCon "Int" []), role := .id} == "Sized.size"
#guard emitVar [{ method := "size", cls := "Sized" }] [] {name := "other", unique := 8, ty := .tyCon "Int" [], role := .id} == "other_8"

-- Dict Task 5: a user-class instance emits `instance : C T where m := <ref>`.
#guard (((emitInstanceUser [sizedClass] [csizeBind, dfunBind] sizedInst).getD "").splitOn
         "instance : Sized (GHCCore.tyConOpaque \"Box\") where").length == 2
#guard (((emitInstanceUser [sizedClass] [csizeBind, dfunBind] sizedInst).getD "").splitOn
         "size := ").length == 2
-- no matching class → none
#guard emitInstanceUser [] [csizeBind, dfunBind] sizedInst == none

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
-- `Generated/UserClass.lean` has today, character for character.
#guard ((m3parseClass m3SizedJson).toOption.map emitClassDecl)
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
#guard emitClassDecl
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
#guard emitClassDecl
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

end GhcCoreToLean.Tests
