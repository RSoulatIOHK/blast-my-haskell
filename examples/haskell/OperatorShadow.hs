{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 Task 2 fixture: the FOURTH cell of `Emit.emitVar`'s method-lookup table —
-- a local binder that is BOTH shadowing a class method AND spelled with a name
-- that has a `Maps.valueMap` image.
--
-- `TwoClassesDistinctMethods.hs` covers the shadowing of an ORDINARY method name
-- (`size`), which has no builtin image: when the shadow test suppressed the
-- `methodMap` match, the fall-through landed in `valueMap`, missed, and reached
-- `refId` — the right answer by accident. An OPERATOR method name does not miss.
-- `valueMap "=="` is `(· == ·)`, so the suppressed match fell through to the
-- BUILTIN. OBSERVED on this fixture before the fix:
--
--     def applyEq (_eq__eq__9645 : (Int → Int → Bool)) (p_9646 : Int)
--         (q_9647 : Int) : Bool :=
--       (((fun a b => a == b))) (p_9646)) (q_9647)
--
-- which Lean accepts (`BEq Int` is in scope) with only an `unused variable`
-- warning, and whose property `applyEq_uses_its_argument` blaster FALSIFIED.
-- The argument is discarded and the body is builtin equality on `Int`.
--
-- WHAT THIS FIXTURE NEEDS TO BE, and why each part is load-bearing:
--
--   * `import Prelude hiding ((==))` — declaring `(==)` is otherwise a duplicate.
--   * A real `instance MyEq Box`, so a `$c==` bind survives and
--     `reconstructClasses` puts `("==", "MyEq")` in the method→class map.
--     Without the instance, `Emit.unmappedOperatorMethods` REFUSES the module
--     (a declared operator method with no map entry) and nothing reaches
--     `emitVar` at all.
--   * NO `deriving Eq` on `Box` — that is the `UserClassNeqWithEq.hs` shape,
--     where two same-head `$c` binds are both dropped and the refusal fires.
--   * ONE equation over a single-constructor type: a multi-equation method makes
--     GHC build a `fail` join point applied to `void#`, which has no `valueMap`
--     image (see `UserClassNeq.hs`) — a real but unrelated gap.
--   * `applyEq` MONOMORPHIC at `Int`: a `MyEq a =>` signature would make the
--     body a dict-selector application, with no bare `==` `Var` to shadow.
--
-- The instance body is deliberately NOT equality (`a > b`), so the non-shadowed
-- direction is discriminating too: `eqBox_uses_the_class_method` holds for the
-- user's method and fails for the builtin `==`.
module OperatorShadow where
    import Prelude hiding ((==))
    import Lean.Spec (lean)

    class MyEq a where
        (==) :: a -> a -> Bool

    data Box = Box Int

    instance MyEq Box where
        (Box a) == (Box b) = a > b

    -- NON-shadowed call site: must rewrite to the user's `MyEq.==`.
    eqBox :: Box -> Box -> Bool
    eqBox a b = a == b

    -- SHADOWED call site: the parameter is named `(==)`, so `p == q` is an
    -- application of the PARAMETER, not of the class method and not of the
    -- builtin.
    applyEq :: (Int -> Int -> Bool) -> Int -> Int -> Bool
    applyEq (==) p q = p == q

    [lean|
    theorem eqBox_uses_the_class_method :
        ∀ (m n : Int), eqBox (Box.Box m) (Box.Box n) = (m > n) := by blaster

    theorem applyEq_uses_its_argument :
        ∀ (p q : Int), applyEq (fun _ _ => false) p q = false := by blaster
    |]
