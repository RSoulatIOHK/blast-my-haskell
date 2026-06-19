import GhcCoreToLean.Maps
import GhcCoreToLean.Emit
import GhcCoreToLean.AST

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

-- Task 5: partial library functions collapse to `default` like error/undefined.
def headApp : Expr :=
  .app (.var {name := "GHC.List.head", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "xs", unique := 1, ty := .tyCon "List" [.tyVar "a"], role := .id})
#guard emitExpr [] headApp == "default"

def fromJustApp : Expr :=
  .app (.var {name := "Data.Maybe.fromJust", unique := 0, ty := .tyVar "a", role := .id})
       (.var {name := "m", unique := 1, ty := .tyCon "Maybe" [.tyVar "a"], role := .id})
#guard emitExpr [] fromJustApp == "default"

end GhcCoreToLean.Tests
