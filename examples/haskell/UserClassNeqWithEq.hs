{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- NEGATIVE fixture: transpilation MUST fail. `./transpile.sh
-- examples/haskell/UserClassNeqWithEq.hs` is expected to exit 1 with an error
-- naming `Neq` and `/=`, and to produce no
-- GhcCoreToLean/Generated/UserClassNeqWithEq.lean. Deliberately EXCLUDED from the
-- green-regression list, like NewtypeInstances.hs.
--
-- It is `UserClassNeq.hs` plus `deriving Eq` on the instance head, which is the
-- one shape where M3 Task 2's `$c/=` scoping cannot win: GHC emits BOTH the Eq
-- instance's `$c/=` and this class's `$c/=` with the same name and the same first
-- argument type (`Box`), distinguishable only by unique, so `Emit.isEqNeqBind`'s
-- head-type test drops both. The method→class map then has no `/=` entry and the
-- call site falls through to `Maps.valueMap`'s BUILTIN `/=`.
--
-- Before `Emit.unmappedOperatorMethods` that fell through SILENTLY — observed:
--
--     def differs (a_9642 : Box) (b_9643 : Box) : Bool :=
--       (((fun a b => !(a == b))) (a_9642)) (b_9643)
--
-- which Lean accepted (the `deriving Eq` supplied `BEq Box`) and which never
-- calls the class method. That is silently wrong for any class whose operator
-- means something other than the builtin, so the program is refused instead.
-- Note what that trade is: this module DID transpile before (wrongly), so the
-- refusal is a deliberate reachability regression for this shape — the honest
-- state is "was silent-wrong, is now refused", not "now correct".
--
-- The precise fix (attributing each `$c` bind to its instance through the dfun
-- body's method-ref UNIQUES, rather than by head-type string) would let this
-- module transpile correctly; it also needs `emitFullProgram`'s
-- `isSuppressedMethod` to stop being name+head keyed, which is why it is a
-- follow-up rather than part of Task 2.
module UserClassNeqWithEq where
    import Prelude hiding ((/=))

    class Neq a where
        (/=) :: a -> a -> Bool

    data Box = Box Int deriving Eq

    instance Neq Box where
        (Box a) /= (Box b) = a > b || b > a

    differs :: Box -> Box -> Bool
    differs a b = a /= b
