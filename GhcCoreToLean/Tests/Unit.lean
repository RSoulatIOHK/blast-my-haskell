import GhcCoreToLean.Maps
import GhcCoreToLean.Emit
import GhcCoreToLean.AST
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
def sizedClass : ClassDecl :=
  { name := "Sized", tyVar := "a",
    methods := [ { name := "size", ty := .tyFun (.tyVar "a") (.tyCon "Int" []) } ] }
#guard sizedClass.name == "Sized"
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
#guard reconRes.2 == [("size", "Sized")]
#guard emitType (reconRes.1.head!).methods.head!.ty == emitType (.tyFun (.tyVar "a") (.tyCon "Int" []))

-- Dict Task 3: emit a Lean `class` from a ClassDecl.
#guard emitClassDecl sizedClass == "class Sized (a : Type) where\n  size : (a → Int)"

-- Dict Task 4: a bare class-method selector emits `Class.method`; others unaffected.
#guard emitVar [("size","Sized")] [] {name := "size", unique := 7, ty := .tyFun (.tyVar "a") (.tyCon "Int" []), role := .id} == "Sized.size"
#guard emitVar [("size","Sized")] [] {name := "other", unique := 8, ty := .tyCon "Int" [], role := .id} == "other_8"

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

end GhcCoreToLean.Tests
