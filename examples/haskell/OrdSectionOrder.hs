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
-- sweep. Sections (1)-(5) are those five.
--
-- Sections (6) and (7) are two later, SILENT ones, both in the mechanism that
-- fixed (4): the user's `BEq` is spliced ahead of the compare def only if the `==`
-- is DETECTED, and detection read a value argument's type. (6) is an `==` with no
-- bare-`Var` argument — nothing detected, nothing hoisted. (7) is a self-recursive
-- hand-written `Eq`, where the hoist necessarily puts the def before the instance
-- it backs, so the recursive `==` inside it stayed structural. Detection now reads
-- the pre-`Lower` TYPE APPLICATION (`Emit.classOpHeadTy`) and the self-call is
-- retargeted (`Emit.retargetSelfEq`).
--
-- Every hand-written `Ord` block is spliced into the DATA BLOCK, each next to its
-- own `inductive`, in `sortDataDecls`' order widened by the compare-body reference
-- graph. See `Emit.emitFullProgram`'s "WHY THE DATA BLOCK" comment for the
-- measured failure of every other layout, and the `M3T6O`/`M3T6E` blocks in
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

    -- (6) THE COMPOUND-ARGUMENT SHAPE. Same silent defect as (4), one step
    -- further: the `==` inside `compare` has no bare-`Var` argument at all, so the
    -- detection that fixed (4) — read the first `Var` argument's type, post-`Lower`
    -- — found nothing and the hoist never happened. `Frac2` above is detected only
    -- because GHC's `x@(Frac2 a b)` binder makes `x` a `Var`; drop the as-pattern
    -- and the very same instance goes silent again. Detection now reads the TYPE
    -- APPLICATION (`== @Cross $fEqCross …`, present pre-`Lower`), which no argument
    -- shape can hide. Measured with the pre-fix binary: transpiler stderr empty and
    -- `decide` PROVED `crossCompare (Cross 1 2) (Cross 2 4) = Ordering.eq` FALSE.
    data Cross = Cross Int Int

    instance Eq Cross where
        Cross a b == Cross c d = a * d == c * b

    instance Ord Cross where
        compare (Cross a b) (Cross c d)
            | Cross a b == Cross c d = EQ
            | a * d < c * b          = LT
            | otherwise              = GT

    crossCompare :: Cross -> Cross -> Ordering
    crossCompare = compare

    crossEq :: Cross -> Cross -> Bool
    crossEq = (==)

    -- (7) A SELF-RECURSIVE hand-written `Eq`, hoisted. The hoist puts the `$c==`
    -- def ahead of the `instance : BEq PList` it backs — it has to, the instance
    -- references the def — so the recursive `as == bs` INSIDE that body was the one
    -- `==` still resolving to `instBEqOfDecidableEq`. Parity equality is therefore
    -- correct at depth 1 and silently STRUCTURAL at depth ≥ 2. `retargetSelfEq`
    -- points the recursive call at the def being emitted, the way
    -- `retargetSelfCompare` already did for `compare` — but keyed on the type
    -- application, because a MISSED `compare` is loud (`failed to synthesize Ord`)
    -- and a missed `==` is not.
    --
    -- Written with nested `case`s rather than overlapping equations so GHC emits no
    -- `void#` join point (which has no Lean image and would make this loud for an
    -- unrelated reason).
    data PList = PNil | PCons Int PList

    instance Eq PList where
        PNil == y = case y of
            PNil      -> True
            PCons _ _ -> False
        PCons a as == y = case y of
            PNil       -> False
            PCons b bs -> (a `mod` 2 == b `mod` 2) && (as == bs)

    instance Ord PList where
        compare x y
            | x == y    = EQ
            | otherwise = LT

    plistEq :: PList -> PList -> Bool
    plistEq = (==)

    plistCompare :: PList -> PList -> Ordering
    plistCompare = compare

    -- (8) The SAME self-recursive `Eq` defect on a head that is NOT hoisted: this
    -- `compare` never mentions `==`/`/=` at `QList`, so nothing about the `Ord`
    -- pulls the `Eq` into the data block. It does not need to — the `$c==` def
    -- precedes `instance : BEq QList` in the ORDINARY layout too (the instance
    -- references the def, and the whole instance section follows the method-def
    -- section), and `deriving … DecidableEq` is on the `inductive` because the
    -- `Ord` takes the hand-written route. So the recursive `as == bs` was
    -- structural here as well, with the transpiler silent. `eqHoistHeads` now
    -- SEEDS on "this `Eq` recurses at its own head" (`Emit.selfEqHeads`)
    -- independently of any `compare`, which routes the head through the same
    -- retarget-and-splice path as (7).
    --
    -- Section (7) alone would NOT have caught this: `PList`'s `compare` tests
    -- `x == y`, so its head was hoisted for the (4) reason and the retarget rode
    -- along.
    data QList = QNil | QCons Int QList

    instance Eq QList where
        QNil == y = case y of { QNil -> True; QCons _ _ -> False }
        QCons a as == y = case y of
            QNil       -> False
            QCons b bs -> (a `mod` 2 == b `mod` 2) && (as == bs)

    instance Ord QList where
        compare x y = case x of
            QNil      -> case y of { QNil -> EQ; QCons _ _ -> LT }
            QCons a _ -> case y of { QNil -> GT; QCons b _ -> compare a b }

    qlistEq :: QList -> QList -> Bool
    qlistEq = (==)

    qlistLt :: QList -> QList -> Bool
    qlistLt = (<)

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

    -- (6) The COMPOUND-ARGUMENT `==` inside `compare`: same divergence as (4), on
    -- an instance with no bare-`Var` argument anywhere in the comparison. `decide`
    -- PROVED the second of these FALSE before the type-application read.
    [lean|
    theorem crossEq_crossMultiplies :
        crossEq (Cross.Cross 1 2) (Cross.Cross 2 4) = true := by decide
    |]

    [lean|
    theorem crossCompare_agreesWithEq :
        crossCompare (Cross.Cross 1 2) (Cross.Cross 2 4) = Ordering.eq := by decide
    |]

    [lean|
    theorem crossCompare_strictlyGreater :
        crossCompare (Cross.Cross 3 2) (Cross.Cross 1 2) = Ordering.gt := by decide
    |]

    [lean|
    theorem crossCompare_strictlyLess :
        crossCompare (Cross.Cross 1 2) (Cross.Cross 3 2) = Ordering.lt := by decide
    |]

    -- (7) The SELF-RECURSIVE hand-written `Eq`. Depth 1 agrees with the structural
    -- order (both tails are `PNil`), so it is the no-regression check; depth 2 is
    -- the discriminator, and `decide` PROVED it FALSE before `retargetSelfEq`.
    [lean|
    theorem plistEq_depth1 :
        plistEq (PList.PCons 1 PList.PNil) (PList.PCons 3 PList.PNil) = true := by decide
    |]

    [lean|
    theorem plistEq_depth2 :
        plistEq (PList.PCons 1 (PList.PCons 2 PList.PNil))
                (PList.PCons 3 (PList.PCons 4 PList.PNil)) = true := by decide
    |]

    -- Parity really is parity: differing parity at depth 2 is NOT equal, so the
    -- recursion is doing the comparison rather than being short-circuited.
    [lean|
    theorem plistEq_depth2_differs :
        plistEq (PList.PCons 1 (PList.PCons 2 PList.PNil))
                (PList.PCons 3 (PList.PCons 5 PList.PNil)) = false := by decide
    |]

    -- …and the hand-written `compare` reads that `Eq`, which is what puts the
    -- hoisted `$c==` in the data block in the first place.
    [lean|
    theorem plistCompare_depth2 :
        plistCompare (PList.PCons 1 (PList.PCons 2 PList.PNil))
                     (PList.PCons 3 (PList.PCons 4 PList.PNil)) = Ordering.eq := by decide
    |]

    -- (8) The same recursion, at a head NOTHING hoists. Depth 2 is the
    -- discriminator and `decide` PROVED it FALSE until `eqHoistHeads` seeded on
    -- the self-recursion itself.
    [lean|
    theorem qlistEq_depth1 :
        qlistEq (QList.QCons 1 QList.QNil) (QList.QCons 3 QList.QNil) = true := by decide
    |]

    [lean|
    theorem qlistEq_depth2 :
        qlistEq (QList.QCons 1 (QList.QCons 2 QList.QNil))
                (QList.QCons 3 (QList.QCons 4 QList.QNil)) = true := by decide
    |]

    [lean|
    theorem qlistEq_depth2_differs :
        qlistEq (QList.QCons 1 (QList.QCons 2 QList.QNil))
                (QList.QCons 3 (QList.QCons 5 QList.QNil)) = false := by decide
    |]

    -- The `Ord` is untouched by the hoist — it still orders by the first field,
    -- which is what pins that relocating the `Eq` did not disturb it.
    [lean|
    theorem qlistLt_firstFieldWins :
        qlistLt (QList.QCons 1 QList.QNil) (QList.QCons 2 QList.QNil) = true := by decide
    |]
