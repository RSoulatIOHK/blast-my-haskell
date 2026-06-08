{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}

module Ratio where

data CustomRatio =
    CustomRatio {numerator :: Integer,
     denominator :: Integer} deriving (Show)

instance Eq CustomRatio where
    (CustomRatio n1 d1) == (CustomRatio n2 d2) =
        n1 * d2 == n2 * d1

addRatio :: CustomRatio -> CustomRatio -> CustomRatio
addRatio (CustomRatio n1 d1) (CustomRatio n2 d2) =
    CustomRatio (n1 * d2 + n2 * d1) (d1 * d2)

{- @lean theorem addRatio_correct :
    ∀ (n1 d1 n2 d2 : Int), d1 > 0 → d2 > 0 →
    addRatio (CustomRatio.CustomRatio n1 d1) (CustomRatio.CustomRatio n2 d2) =
    CustomRatio.CustomRatio (n1 * d2 + n2 * d1) (d1 * d2) := by blaster -}
    
subRatio :: CustomRatio -> CustomRatio -> CustomRatio
subRatio (CustomRatio n1 d1) (CustomRatio n2 d2) =
    CustomRatio (n1 * d2 - n2 * d1) (d1 * d2)

multRatio :: CustomRatio -> CustomRatio -> CustomRatio
multRatio (CustomRatio n1 d1) (CustomRatio n2 d2) =
    CustomRatio (n1 * n2) (d1 * d2)

integerAddRatio :: Integer -> CustomRatio -> CustomRatio
integerAddRatio i (CustomRatio n d) =
    CustomRatio (i * d + n) d

integerSubRatio :: Integer -> CustomRatio -> CustomRatio
integerSubRatio i (CustomRatio n d) =
    CustomRatio (i * d - n) d

integerMultRatio :: Integer -> CustomRatio -> CustomRatio
integerMultRatio i (CustomRatio n d) =
    CustomRatio (i * n) d

-- Batch 1: functions exercising the new primitives (abs, quot, mod, negate, if).

absRatio :: CustomRatio -> CustomRatio
absRatio (CustomRatio n d) = CustomRatio (abs n) d

truncateRatio :: CustomRatio -> Integer
truncateRatio (CustomRatio n d) = quot n d

-- Divides an integer by a ratio and truncates. Errors implicitly if ratio is 0.
truncateRecipRatio :: Integer -> CustomRatio -> Integer
truncateRecipRatio i (CustomRatio n d) = quot (i * d) n

ceilRatio :: CustomRatio -> Integer
ceilRatio (CustomRatio n d) =
    let r = quot n d
    in if d * r < n then r + 1 else r

normalizeRatio :: CustomRatio -> CustomRatio
normalizeRatio cr@(CustomRatio n d) =
    if d < 0 then CustomRatio (negate n) (negate d) else cr

recipRatio :: CustomRatio -> CustomRatio
recipRatio (CustomRatio n d) = CustomRatio d n

gcdInt :: Integer -> Integer -> Integer
gcdInt a b = if b == 0 then a else gcdInt b (mod a b)

-- Batch 2: predicates (only confirmed operators) and gcd-based reduction check.

-- Binary predicates between ratios. NOTE: assume non-zero denominators.
ratioEq :: CustomRatio -> CustomRatio -> Bool
ratioEq (CustomRatio n1 d1) (CustomRatio n2 d2) = n1 * d2 == n2 * d1

ratioLt :: CustomRatio -> CustomRatio -> Bool
ratioLt (CustomRatio n1 d1) (CustomRatio n2 d2) = n1 * d2 < n2 * d1

ratioLeq :: CustomRatio -> CustomRatio -> Bool
ratioLeq (CustomRatio n1 d1) (CustomRatio n2 d2) = n1 * d2 <= n2 * d1

ratioGt :: CustomRatio -> CustomRatio -> Bool
ratioGt (CustomRatio n1 d1) (CustomRatio n2 d2) = n1 * d2 > n2 * d1

ratioGeq :: CustomRatio -> CustomRatio -> Bool
ratioGeq (CustomRatio n1 d1) (CustomRatio n2 d2) = n1 * d2 >= n2 * d1

-- Binary predicates between an integer and a ratio.
integerLtRatio :: Integer -> CustomRatio -> Bool
integerLtRatio i (CustomRatio n d) = d * i < n

integerLeqRatio :: Integer -> CustomRatio -> Bool
integerLeqRatio i (CustomRatio n d) = d * i <= n

integerGtRatio :: Integer -> CustomRatio -> Bool
integerGtRatio i (CustomRatio n d) = i * d > n

integerGeqRatio :: Integer -> CustomRatio -> Bool
integerGeqRatio i (CustomRatio n d) = i * d >= n

-- Binary predicates between a ratio and an integer (defined via the above).
ratioLtInteger :: CustomRatio -> Integer -> Bool
ratioLtInteger r i = integerGtRatio i r

ratioLeqInteger :: CustomRatio -> Integer -> Bool
ratioLeqInteger r i = integerGeqRatio i r

ratioGtInteger :: CustomRatio -> Integer -> Bool
ratioGtInteger r i = integerLtRatio i r

ratioGeqInteger :: CustomRatio -> Integer -> Bool
ratioGeqInteger r i = integerLeqRatio i r

-- Returns true if the numerator is positive. NOTE: assumes non-zero denominator.
isPositive :: CustomRatio -> Bool
isPositive (CustomRatio n d) = n > 0

-- Checks whether the ratio is reduced (numerator and denominator coprime).
isReduced :: CustomRatio -> Bool
isReduced (CustomRatio n d) = gcdInt n d == 1

-- The largest denominator considered to have "max precision" (10 ^ 6).
maxRatioPrecision :: Integer
maxRatioPrecision = 1000000

hasMaxPrecision :: CustomRatio -> Bool
hasMaxPrecision (CustomRatio n d) = d <= maxRatioPrecision

-- Batch 3: adapted Plutarch glue. The Plutarch originals decode `BuiltinData`
-- and thread results through a continuation `(... -> Term s r) -> Term s r`.
-- In plain Haskell the continuation is an ordinary function argument, and
-- `ptraceInfoError` becomes `error` (a bottom, like the Plutarch trace-error).

-- SOP (sum-of-product) representation. Structurally a second ratio type.
data CustomRatioSOP =
    CustomRatioSOP { snumerator :: Integer,
     sdenominator :: Integer} deriving (Show)

instance Eq CustomRatioSOP where
    (CustomRatioSOP n1 d1) == (CustomRatioSOP n2 d2) =
        n1 * d2 == n2 * d1

-- Makes a ratio from a numerator and denominator. Does not check the sign.
mkRatioUnsafe :: Integer -> Integer -> CustomRatio
mkRatioUnsafe n d = CustomRatio n d

-- Pattern-matches a ratio into its numerator and denominator fields.
unsafeRatioMatch :: CustomRatio -> (Integer -> Integer -> b) -> b
unsafeRatioMatch (CustomRatio n d) f = f n d

-- Binds (let-floats) a ratio through a continuation.
bindRatio :: CustomRatio -> (CustomRatio -> r) -> r
bindRatio (CustomRatio n d) k = k (CustomRatio n d)

-- Converts an SOP ratio to the working ratio through a continuation.
fromRatioSOPUnsafe :: CustomRatioSOP -> (CustomRatio -> r) -> r
fromRatioSOPUnsafe (CustomRatioSOP n d) k = k (CustomRatio n d)

-- As above, but errors when the denominator is not positive.
fromRatioSOPSafe :: CustomRatioSOP -> (CustomRatio -> r) -> r
fromRatioSOPSafe (CustomRatioSOP n d) k =
    if d > 0 then k (CustomRatio n d)
    else error "fromRatioSOPSafe: division by zero"

-- Matches a ratio, checking the denominator is positive and the fraction
-- reduced (gcd == 1); errors otherwise.
safeRatioMatch :: CustomRatio -> (CustomRatio -> b) -> b
safeRatioMatch (CustomRatio n d) f =
    if d > 0
      then if gcdInt n d == 1
             then f (CustomRatio n d)
             else error "safeRatioMatch: gcd(numerator, denominator) should be 1"
      else error "safeRatioMatch: denominator should be positive"

-- Ensures the denominator is positive, pushing any sign onto the numerator.
normalizeRatioC :: CustomRatio -> (CustomRatio -> r) -> r
normalizeRatioC cr@(CustomRatio n d) k =
    if d < 0 then k (CustomRatio (negate n) (negate d)) else k cr

-- Reciprocal through a continuation; errors when the numerator is zero.
recipC :: CustomRatio -> (CustomRatio -> r) -> r
recipC (CustomRatio n d) k =
    if n == 0 then error "recipC: division by zero"
    else normalizeRatioC (CustomRatio d n) k

-- Multiplies a ratio by the reciprocal of an integer; errors on zero.
integerRecipMulRatioC :: Integer -> CustomRatio -> (CustomRatio -> r) -> r
integerRecipMulRatioC i (CustomRatio n d) k =
    if i == 0 then error "integerRecipMulRatioC: division by zero"
    else normalizeRatioC (CustomRatio n (i * d)) k

-- Reduces a ratio to simplest form. Expensive; not for on-chain use.
reduceRatio :: CustomRatio -> CustomRatio
reduceRatio (CustomRatio n d) =
    let g = gcdInt n d
    in CustomRatio (quot n g) (quot d g)

reduceC :: CustomRatio -> (CustomRatio -> r) -> r
reduceC cr k = k (reduceRatio cr)

-- Batch 4: ported from FullRatio.hs (the fuller Cardano source). Only the
-- behaviour Ratio.hs did not already have; the rest of FullRatio duplicates
-- functions above (e.g. its `abs`/`truncate`/`ceil`/`unsafeRecip` are this
-- file's `absRatio`/`truncateRatio`/`ceilRatio`/`recipRatio`). Bare Plutus
-- names are given the `*Ratio` suffix here to avoid shadowing the Prelude.
-- NOTE: this file's `normalizeRatio` takes a CustomRatio (it flips the sign
-- when d < 0), so the constructors below build then normalize.

-- Safe constructor: Nothing on a zero denominator, otherwise normalized.
mkRatioSafe :: Integer -> Integer -> Maybe CustomRatio
mkRatioSafe n d = if d == 0 then Nothing else Just (normalizeRatio (CustomRatio n d))

-- Constructor that errors on a non-positive denominator.
tryMkRatio :: Integer -> Integer -> CustomRatio
tryMkRatio n d =
    if d <= 0 then error "tryMkRatio: negative or zero denominator"
    else CustomRatio n d

-- The integer n as the ratio n/1.
fromIntegerRatio :: Integer -> CustomRatio
fromIntegerRatio n = CustomRatio n 1

zeroRatio :: CustomRatio
zeroRatio = CustomRatio 0 1

halfRatio :: CustomRatio
halfRatio = CustomRatio 1 2

oneRatio :: CustomRatio
oneRatio = CustomRatio 1 1

-- Additive inverse: negate the numerator.
negateRatio :: CustomRatio -> CustomRatio
negateRatio (CustomRatio n d) = CustomRatio (negate n) d

-- Multiplies a ratio by the reciprocal of an integer; errors on zero.
-- (The direct form of integerRecipMulRatioC above.)
recipMulRatio :: Integer -> CustomRatio -> CustomRatio
recipMulRatio i (CustomRatio n d) =
    if i == 0 then error "recipMulRatio: integer is zero"
    else normalizeRatio (CustomRatio n (d * i))

-- Reciprocal that errors on a zero numerator and normalizes the sign.
-- (recipRatio above is the unsafe swap; this is FullRatio's safe `recip`.)
safeRecipRatio :: CustomRatio -> CustomRatio
safeRecipRatio (CustomRatio n d) =
    if n == 0 then error "safeRecipRatio: zero numerator"
    else normalizeRatio (CustomRatio d n)

