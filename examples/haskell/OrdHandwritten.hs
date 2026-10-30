{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 Task 6 fixture: HAND-WRITTEN, non-structural `Ord`.
--
-- Until this task `ordTypes` was INSTANCE-EXISTENCE-based: any type with an `Ord`
-- instance got Lean `deriving Ord` and its real `$ccompare`/`$c<`/… bodies were
-- dropped. So every instance below was silently replaced by Lean's STRUCTURAL
-- order — the one failure mode this project forbids. `Emit.ordRoute` now decides
-- per instance (derived / hand-written / unsupported); see its section header for
-- the discriminators and both misclassification directions, and the `M3 Task 6`
-- block in GhcCoreToLean/Tests/Unit.lean for the dump spines and the A/B.
--
-- Every property here is written to FALSIFY under the structural order and hold
-- under the Haskell one — which is what makes them a test rather than a smoke
-- check. Measured with the pre-task binary, `Rev`'s and `Frac`'s properties are
-- not merely unproven but REFUTED: `decide` proves the Haskell truth false.
--
-- All four routes live side by side on purpose:
--
--   * `Rev`, `Frac`  — hand-written `compare` (`instance : Ord T where compare := …`
--                      plus the LE/LT/Min/Max companions derived from it).
--   * `Rank`         — derived on an enum: tag primops ⇒ `deriving Ord`, the
--                      pre-task treatment, byte-for-byte unchanged.
--   * `Pair`         — derived on a SINGLE-constructor type: no tag comparison is
--                      needed, so GHC's derived `compare` has no primop and is
--                      classified hand-written. Sound: the derived body IS the
--                      derived order (field-lexicographic), and these properties
--                      say so.
--   * `MinDef`       — a minimal `(<=)`-only instance, whose `compare` is GHC's
--                      dictionary-dependent class default. Not translatable, so
--                      NO `Ord` is emitted and the transpiler warns; nothing
--                      structural is substituted. Its order is deliberately never
--                      used, so the module still compiles.
module OrdHandwritten where
    import Prelude
    import Lean.Spec (lean)

    -- REVERSED order on a one-field type: the sharpest discriminator, because
    -- structural and reversed disagree on every distinct pair.
    data Rev = Rev Int

    instance Eq Rev where
        Rev a == Rev b = a == b

    instance Ord Rev where
        compare (Rev a) (Rev b) = compare b a

    revLt :: Rev -> Rev -> Bool
    revLt a b = a < b

    revCompare :: Rev -> Rev -> Ordering
    revCompare a b = compare a b

    -- `min` is the COMPANION path (`instance : Min Rev := minOfLe`, off `leOfOrd`,
    -- off the hand-written `compare`), so this is what pins that the companions
    -- follow the user's order rather than the structural one.
    revMin :: Rev -> Rev -> Rev
    revMin a b = min a b

    -- Cross-multiply order on a two-field ratio-like type. `Frac a b` reads as the
    -- rational a/b (all denominators positive in the properties below), so
    -- `Frac 1 2 > Frac 2 5` while the structural order says the opposite.
    data Frac = Frac Int Int

    -- Hand-written `Eq` as well. `Frac` therefore has TWO `BEq` routes — this
    -- instance, and core's `instBEqOfDecidableEq` over `deriving DecidableEq` — and
    -- the explicit one must win, or an `Eq`-constrained call here would report
    -- structural equality (M3 Task 3's `M3T3R` hazard). What CHANGED is the reason
    -- route 1 exists: pre-task it came from `deriving Ord`; now it comes from the
    -- `DecidableEq` that Task 6 emits precisely because there is no `deriving Ord`
    -- any more. `fracEq_crossMultiplies` below is therefore a NO-REGRESSION check,
    -- not a discriminator — it holds with both binaries (measured). The `M3T6R`
    -- `#guard`s in Tests/Unit.lean are the ones that pin the selection in the new
    -- section order (`Ord` from an instance block rather than from `deriving`).
    instance Eq Frac where
        Frac a b == Frac c d = a * d == c * b

    instance Ord Frac where
        compare (Frac a b) (Frac c d) = compare (a * d) (c * b)

    fracLt :: Frac -> Frac -> Bool
    fracLt x y = x < y

    fracEq :: Frac -> Frac -> Bool
    fracEq x y = x == y

    -- A BUILTIN-`Ord`-constrained call (M3 Task 3's binder recipe: `[Ord t] [LT t]
    -- [LE t] [DecidableLT t] [DecidableLE t] [Min t] [Max t] [BEq t]`) applied at a
    -- hand-written-`Ord` head. Before this task every one of those binders resolved
    -- — against the WRONG (structural) order.
    minOf :: Ord a => a -> a -> a
    minOf x y = if x <= y then x else y

    fracMin :: Frac -> Frac -> Frac
    fracMin = minOf

    -- Task 5's loud→silent REGRESSION, closed here. `class Ord a => Capped a` is a
    -- user class with a BUILTIN superclass, so `Capped a => …` emits the parent's
    -- binder recipe at every constraint site. At the pre-Task-5 parent that made
    -- `cappedOrdered` fail LOUD (`failed to synthesize LT t`); Task 5 supplied the
    -- binders and the call at a hand-written-`Ord` head began to elaborate against
    -- the structural order instead — silent. It is faithful again only because the
    -- root cause is gone.
    class Ord a => Capped a where
        cap :: a -> a -> a

    -- `cap`'s body uses the PARENT's operator at `Frac` — `min`, which comes from
    -- the `Min Frac` companion off the hand-written `compare`. That is the shape
    -- that forced hand-written `Ord` into its own emission section: a `$c` method
    -- def like this one is emitted before the instance section, so with the `Ord`
    -- and its companions in that section `min` here was a forward reference and
    -- failed LOUD. `emitFullProgram` now emits each hand-written `Ord` (def,
    -- instance, companions) ahead of every other method def.
    instance Capped Frac where
        cap x y = min x y

    -- The parent's operator under only the CHILD's constraint — SuperClass.hs's
    -- `capOrdered` shape, at a head whose `Ord` is the user's.
    cappedOrdered :: Capped a => a -> a -> Bool
    cappedOrdered x y = x < y

    fracOrdered :: Frac -> Frac -> Bool
    fracOrdered = cappedOrdered

    fracCap :: Frac -> Frac -> Frac
    fracCap = cap

    -- DERIVED on an enum: `$ccompare` uses `dataToTag#`, so this keeps the
    -- `deriving Ord` route unchanged (the pre-task treatment for every type).
    data Rank = Low | Mid | High deriving (Eq, Ord)

    rankLt :: Rank -> Rank -> Bool
    rankLt a b = a < b

    rankMin :: Rank -> Rank -> Rank
    rankMin a b = min a b

    -- DERIVED on a single-constructor type: one constructor means no tag to
    -- compare, so GHC's derived `compare` contains no primop and this type takes
    -- the HAND-WRITTEN route. The emitted instance points at GHC's own derived
    -- body (`case compare a1 b1 of LT -> LT; EQ -> compare a2 b2; GT -> GT`), so
    -- the order is field-lexicographic either way — that misclassification
    -- direction is sound, and these two properties are its evidence.
    data Pair = Pair Int Int deriving (Eq, Ord)

    pairLt :: Pair -> Pair -> Bool
    pairLt a b = a < b

    -- The MINIMAL-DEFINITION shape: `(<=)` only, so GHC synthesises `compare` from
    -- the class default (`if x == y then EQ else if x <= y then LT else GT`), whose
    -- body needs this instance's own dictionary. Untranslatable ⇒ no `Ord MinDef`
    -- is emitted and the transpiler warns; the old behaviour would have silently
    -- installed the structural order (which for `MinDef` is the OPPOSITE of the
    -- one written here). Its order is never used below, so the module compiles.
    data MinDef = MinDef Int

    instance Eq MinDef where
        MinDef a == MinDef b = a == b

    instance Ord MinDef where
        MinDef a <= MinDef b = b <= a

    minDefEq :: MinDef -> MinDef -> Bool
    minDefEq a b = a == b

    -- ---------------------------------------------------------------------------
    -- Properties. Ground `decide` unless noted; each hand-written-`Ord` one is
    -- FALSE under the structural order.

    -- 1 < 2, so the reversed order says `Rev 1 > Rev 2`.
    [lean|
    theorem revLt_isReversed : revLt (Rev.Rev 1) (Rev.Rev 2) = false := by decide
    |]

    [lean|
    theorem revLt_isReversed_other : revLt (Rev.Rev 2) (Rev.Rev 1) = true := by decide
    |]

    [lean|
    theorem revCompare_isReversed :
        revCompare (Rev.Rev 1) (Rev.Rev 2) = Ordering.gt := by decide
    |]

    -- The COMPANION path: `min` off the hand-written `compare` takes the numerically
    -- LARGER field.
    [lean|
    theorem revMin_takesLarger : revMin (Rev.Rev 1) (Rev.Rev 2) = Rev.Rev 2 := by decide
    |]

    -- Quantified, so the whole reversed body is pinned rather than one point.
    [lean|
    theorem revLt_reverses_all :
        ∀ (a b : Int), revLt (Rev.Rev a) (Rev.Rev b) = decide (b < a) := by blaster
    |]

    -- 1/2 > 2/5 (1*5 = 5 > 4 = 2*2), while the structural order says `Frac 1 2 <
    -- Frac 2 5` on the first field alone.
    [lean|
    theorem fracLt_crossMultiplies : fracLt (Frac.Frac 1 2) (Frac.Frac 2 5) = false := by decide
    |]

    [lean|
    theorem fracLt_crossMultiplies_other :
        fracLt (Frac.Frac 2 5) (Frac.Frac 1 2) = true := by decide
    |]

    -- Two `BEq` routes, one answer: 1/2 == 2/4 under cross-multiply, and NOT under
    -- the structural equality that `deriving DecidableEq` also puts in scope.
    [lean|
    theorem fracEq_crossMultiplies : fracEq (Frac.Frac 1 2) (Frac.Frac 2 4) = true := by decide
    |]

    [lean|
    theorem fracLt_all :
        ∀ (a b c d : Int), fracLt (Frac.Frac a b) (Frac.Frac c d) = decide (a * d < c * b)
        := by blaster
    |]

    -- The `Ord a =>`-constrained call at a hand-written-`Ord` head: 2/5 < 1/2, so
    -- `minOf` returns 2/5 where the structural order would return 1/2.
    [lean|
    theorem fracMin_underOrdConstraint :
        fracMin (Frac.Frac 1 2) (Frac.Frac 2 5) = Frac.Frac 2 5 := by decide
    |]

    -- Task 5's regression, closed: the PARENT's `<` reached through the CHILD's
    -- constraint, at a head whose `Ord` is the user's.
    [lean|
    theorem fracOrdered_viaCapped :
        fracOrdered (Frac.Frac 1 2) (Frac.Frac 2 5) = false := by decide
    |]

    [lean|
    theorem fracOrdered_viaCapped_other :
        fracOrdered (Frac.Frac 2 5) (Frac.Frac 1 2) = true := by decide
    |]

    -- The child's own method, whose body reaches the PARENT's `min` at this head:
    -- 2/5 < 1/2, so `cap` returns 2/5 where the structural order would return 1/2.
    [lean|
    theorem fracCap_takesLower :
        fracCap (Frac.Frac 1 2) (Frac.Frac 2 5) = Frac.Frac 2 5 := by decide
    |]

    [lean|
    theorem fracCap_takesLower_other :
        fracCap (Frac.Frac 2 5) (Frac.Frac 1 2) = Frac.Frac 2 5 := by decide
    |]

    -- The DERIVED route, unchanged: constructor order.
    [lean|
    theorem rankLt_isDerived : rankLt Rank.Low Rank.High = true := by decide
    |]

    [lean|
    theorem rankMin_takesLower : rankMin Rank.High Rank.Mid = Rank.Mid := by decide
    |]

    -- The derived-read-as-hand-written direction: field-lexicographic, i.e. exactly
    -- what `deriving Ord` computes.
    [lean|
    theorem pairLt_firstFieldWins : pairLt (Pair.Pair 1 5) (Pair.Pair 2 0) = true := by decide
    |]

    [lean|
    theorem pairLt_secondFieldBreaksTies :
        pairLt (Pair.Pair 1 5) (Pair.Pair 1 6) = true := by decide
    |]

    [lean|
    theorem pairLt_irreflexive : pairLt (Pair.Pair 1 5) (Pair.Pair 1 5) = false := by decide
    |]

    -- `MinDef` keeps its hand-written `Eq` even though its `Ord` is dropped.
    [lean|
    theorem minDefEq_holds : minDefEq (MinDef.MinDef 3) (MinDef.MinDef 3) = true := by decide
    |]
