{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 Task 6 fixture, second half: the ORDER the `Ord` pieces are emitted in,
-- and the RECURSIVE `compare`.
--
-- `OrdHandwritten.hs` covers the ROUTING question (derived vs hand-written vs
-- unsupported). This module covers everything that depends on WHERE the emitted
-- `Ord` lands, which the first release of Task 6 got wrong in five ways at once —
-- every one of them a loud failure on ORDINARY Haskell, and not one of them
-- visible to the rest of the corpus, which is why they survived a byte-identity
-- sweep. Each numbered section below is one of them.
--
-- The four `Ord` blocks are spliced into the DATA BLOCK, each next to its own
-- `inductive`, in `sortDataDecls`' order widened by the compare-body reference
-- graph. See `Emit.emitFullProgram`'s "WHY THE DATA BLOCK" comment for the
-- measured failure of every other layout, and the `M3T6O` block in
-- GhcCoreToLean/Tests/Unit.lean for the unit pins.
module OrdSectionOrder where
    import Prelude
    import Lean.Spec (lean)

    -- (1) A RECURSIVE type with plain `deriving Ord`. No user instance anywhere.
    -- Two constructors, so GHC's derived `compare` carries no tag primop and does
    -- NOT take the `deriving Ord` route; it recurses as `compare @Tree $fOrdTree`,
    -- which puts `$ccompare` in a `Rec` group with the instance's own dictionary
    -- builder — the same group shape a `<=`-only minimal instance produces. Task 6
    -- classified both `.unsupported`, so this module got NO `Ord Tree` at all and
    -- `treeLt` failed `failed to synthesize LT Tree`. `ordRoute` now separates them
    -- (`ownDictOpsAtHead`) and emits the self-recursion as recursion on the def's
    -- own name.
    data Tree = Leaf | Node Tree Tree deriving (Eq, Ord)

    treeLt :: Tree -> Tree -> Bool
    treeLt a b = a < b

    treeCompare :: Tree -> Tree -> Ordering
    treeCompare = compare

    -- (2) A DERIVED-route type with a HAND-WRITTEN-route type as a FIELD. `Inner`
    -- has 2 constructors' worth of fields and no nullary ones, so no tag primop ⇒
    -- hand-written route ⇒ its `Ord` is an instance BLOCK. `Quad` has 3 nullary
    -- constructors ⇒ tag primops ⇒ derived route ⇒ its `Ord` is `deriving Ord` ON
    -- THE INDUCTIVE, which needs `Ord Inner` already in scope. With the `Ord`
    -- section after the data block that was `failed to synthesize Ord Inner`.
    data Inner = Inner Int Int deriving (Eq, Ord)

    data Quad = QA | QB | QC | QD Inner deriving (Eq, Ord)

    quadLt :: Quad -> Quad -> Bool
    quadLt a b = a < b

    -- (3) A compare body that orders a value of ANOTHER hand-written-`Ord` type
    -- which is NOT a field of it. `sortDataDecls`' field graph has no edge between
    -- `Beta` and `Alpha`, so the emitted order followed the dump and, in this
    -- direction, put `Beta`'s block first: `failed to synthesize Ord Alpha`. The
    -- sort now takes the compare-body REFERENCE graph as extra edges.
    --
    -- `Alpha`'s order is REVERSED, so `Beta`'s is too — which is what makes the
    -- properties below discriminate: they are all FALSE under Lean's structural
    -- order, i.e. they fail if `Alpha`'s instance is dropped or replaced.
    data Alpha = Alpha Int deriving Eq

    instance Ord Alpha where
        compare (Alpha x) (Alpha y) = compare y x

    data Beta = Beta Int deriving Eq

    instance Ord Beta where
        compare (Beta x) (Beta y) = compare (Alpha x) (Alpha y)

    betaLt :: Beta -> Beta -> Bool
    betaLt a b = a < b

    -- (4) A compare body calling `==` at its OWN type, where that `Eq` is
    -- hand-written and NON-structural. This was the SILENT one. Task 6 added
    -- `deriving DecidableEq` to every hand-written-`Ord` type (so `Ord`'s `[BEq t]`
    -- constraint recipe can be satisfied), and the `$ccompare` def was emitted
    -- BEFORE the user's `instance : BEq Frac2` — so `==` inside it resolved to
    -- core's `instBEqOfDecidableEq`, i.e. STRUCTURAL equality, with no warning and
    -- no error. Two meanings of `==` in one module. The user's `BEq` is now spliced
    -- ahead of the compare def.
    --
    -- `Frac2 1 2 == Frac2 2 4` is TRUE by cross-multiplication and FALSE
    -- structurally, and `compare` returns `EQ` only on the first reading — so
    -- `fracCompare_agreesWithEq` below is exactly the divergence, and it was
    -- `decide`-PROVED FALSE before this fix.
    data Frac2 = Frac2 Int Int

    instance Eq Frac2 where
        Frac2 a b == Frac2 c d = a * d == c * b

    instance Ord Frac2 where
        compare x@(Frac2 a b) y@(Frac2 c d)
            | x == y        = EQ
            | a * d < c * b = LT
            | otherwise     = GT

    fracCompare :: Frac2 -> Frac2 -> Ordering
    fracCompare = compare

    fracEq :: Frac2 -> Frac2 -> Bool
    fracEq = (==)

    -- (5) A class-body DEFAULT that orders a hand-written-`Ord` head. Class decls
    -- live in the data block, so with the `Ord` section after it this default's
    -- `min` had no `Min Frac2` in scope: `failed to synthesize Min Frac2`, plus a
    -- cascading `Fields missing: tg` on the instance that relies on the default.
    -- Every spliced block now precedes the class decls, which are the last thing in
    -- the data block.
    class Tag a where
        tg :: a -> Frac2 -> Frac2
        tg _ p = min p p

    data Z = Z

    instance Tag Z

    zTg :: Z -> Frac2 -> Frac2
    zTg = tg

    -- -----------------------------------------------------------------------
    -- Properties. All ground `decide`.

    -- (1) The recursive derived order is Haskell's: `Leaf < Node _ _` (constructor
    -- order), and `Node` compares its fields left-to-right.
    [lean|
    theorem treeLt_leafBeforeNode :
        treeLt Tree.Leaf (Tree.Node Tree.Leaf Tree.Leaf) = true := by decide
    |]

    [lean|
    theorem treeLt_nodeNotBeforeLeaf :
        treeLt (Tree.Node Tree.Leaf Tree.Leaf) Tree.Leaf = false := by decide
    |]

    -- The recursive call is what this one needs: both sides are `Node`, so the
    -- answer comes from comparing the FIRST fields, which recurses.
    [lean|
    theorem treeCompare_recursesOnFirstField :
        treeCompare (Tree.Node Tree.Leaf Tree.Leaf)
                    (Tree.Node (Tree.Node Tree.Leaf Tree.Leaf) Tree.Leaf)
          = Ordering.lt := by decide
    |]

    -- …and on the SECOND field when the first ties, which is the other recursion
    -- site in the same body.
    [lean|
    theorem treeCompare_recursesOnSecondField :
        treeCompare (Tree.Node Tree.Leaf Tree.Leaf)
                    (Tree.Node Tree.Leaf (Tree.Node Tree.Leaf Tree.Leaf))
          = Ordering.lt := by decide
    |]

    [lean|
    theorem treeCompare_reflexive :
        treeCompare (Tree.Node Tree.Leaf (Tree.Node Tree.Leaf Tree.Leaf))
                    (Tree.Node Tree.Leaf (Tree.Node Tree.Leaf Tree.Leaf))
          = Ordering.eq := by decide
    |]

    -- (2) `Quad`'s derived order: nullary constructors in declaration order, and
    -- `QD`'s field ordered by `Inner`'s own (spliced) instance.
    [lean|
    theorem quadLt_ctorOrder : quadLt Quad.QC (Quad.QD (Inner.Inner 0 0)) = true := by decide
    |]

    [lean|
    theorem quadLt_usesInnerOrd :
        quadLt (Quad.QD (Inner.Inner 1 1)) (Quad.QD (Inner.Inner 1 2)) = true := by decide
    |]

    [lean|
    theorem quadLt_usesInnerOrd_other :
        quadLt (Quad.QD (Inner.Inner 1 2)) (Quad.QD (Inner.Inner 1 1)) = false := by decide
    |]

    -- (3) `Beta`'s order is `Alpha`'s, which is REVERSED. Both false structurally.
    [lean|
    theorem betaLt_isReversed : betaLt (Beta.Beta 1) (Beta.Beta 2) = false := by decide
    |]

    [lean|
    theorem betaLt_isReversed_other : betaLt (Beta.Beta 2) (Beta.Beta 1) = true := by decide
    |]

    -- (4) The `==` inside `compare` is the USER's, so `compare` agrees with it.
    [lean|
    theorem fracEq_crossMultiplies :
        fracEq (Frac2.Frac2 1 2) (Frac2.Frac2 2 4) = true := by decide
    |]

    -- THE divergence: `decide` proved this FALSE before the `BEq` splice.
    [lean|
    theorem fracCompare_agreesWithEq :
        fracCompare (Frac2.Frac2 1 2) (Frac2.Frac2 2 4) = Ordering.eq := by decide
    |]

    [lean|
    theorem fracCompare_strictlyGreater :
        fracCompare (Frac2.Frac2 3 2) (Frac2.Frac2 1 2) = Ordering.gt := by decide
    |]

    [lean|
    theorem fracCompare_strictlyLess :
        fracCompare (Frac2.Frac2 1 2) (Frac2.Frac2 3 2) = Ordering.lt := by decide
    |]

    -- (5) The class default resolved its `min` at `Frac2`, and the instance that
    -- relies on it has the field. `min p p = p`, so this is the identity — the
    -- point is that it ELABORATES at all.
    [lean|
    theorem zTg_isIdentity :
        fracCompare (zTg Z.Z (Frac2.Frac2 1 2)) (Frac2.Frac2 1 2) = Ordering.eq := by decide
    |]
