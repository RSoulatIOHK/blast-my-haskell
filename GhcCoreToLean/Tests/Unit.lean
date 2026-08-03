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
#guard Hs.splitAt 1 [5, 6, 7] == ([5], [6, 7])
#guard Hs.splitAt (-2) [1] == ([], [1])
#guard Hs.splitAt 9 [1] == ([1], [])
-- Semantic pins for the inline lambdas (negative-clamp + arg order):
#guard ((fun (n : Int) (xs : List Int) => List.take n.toNat xs) 2 [1,2,3]) == [1,2]
#guard ((fun (n : Int) (xs : List Int) => List.take n.toNat xs) (-1) [1,2,3]) == []
#guard ((fun (n : Int) (xs : List Int) => List.drop n.toNat xs) 1 [1,2,3]) == [2,3]
-- `drop` is the one op whose clamp differs in KIND: take/replicate/splitAt-fst
-- clamp to "empty", drop clamps to "unchanged". Pin it directly.
#guard ((fun (n : Int) (xs : List Int) => List.drop n.toNat xs) (-1) [1,2,3]) == [1,2,3]
#guard ((fun (n : Int) (x : Int) => List.replicate n.toNat x) 3 9) == [9,9,9]
#guard ((fun (n : Int) (x : Int) => List.replicate n.toNat x) (-3) 9) == []

end GhcCoreToLean.Tests
