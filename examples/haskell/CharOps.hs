{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module CharOps where

import Data.Char (isDigit, ord)

-- Char LITERALS. `'A'` is the first `Char` literal any dump in this project has
-- ever contained, so this fixture is also what first exercises `Lower`'s `C#`
-- erasure and `Emit.escapeCharLit` on real data rather than on unit guards.
letterA :: Char
letterA = 'A'

digitZero :: Char
digitZero = '0'

-- NON-ASCII literals, emitted RAW (Lean has no `\uXXXX` that spells a non-BMP
-- char, and the generated file is UTF-8 — see `Emit.escapeLitChar`).
accent :: Char
accent = 'é'                    -- U+00E9

-- ARABIC-INDIC DIGIT FIVE, U+0665. A digit to Unicode, not to `isDigit`:
-- `isDigit` is ASCII-only on BOTH sides (Haskell `GHC.Unicode.isDigit` and Lean
-- `Char.isDigit` both test 48..57), which is why it is the one `Data.Char`
-- predicate this transpiler maps. Pinned below in both languages.
arabicFive :: Char
arabicFive = '٥'

-- EQUALITY / ORDERING. `Char`'s Eq and Ord dicts are erased by `Lower`, so
-- these go through the same `classConMap "Ord"` binders as any other type.
-- `min`/`max` at `Char` are deliberately absent — v4.24 has no `Min Char`/
-- `Max Char` instance, so mapping them fails LOUD (plan correction 5). That is
-- the documented negative; there is nothing to add here.
sameChar :: Char -> Char -> Bool
sameChar a b = a == b

charLess :: Char -> Char -> Bool
charLess a b = a < b

charLE :: Char -> Char -> Bool
charLE a b = a <= b

-- `ord` is SAFE in the direction that matters: every Lean `Char` has a faithful
-- Haskell image, so the surrogate gap enters only through CONSTRUCTION. Its
-- inverse `chr` is therefore unmapped and fails loud (plan correction 3).
charCode :: Char -> Int
charCode c = ord c

digitP :: Char -> Bool
digitP c = isDigit c

-- Char literals in PATTERN position — ordinary Haskell, and the first real dump
-- to reach `Emit.emitLiteralPattern`'s `.litChar` arm (for `LitString` that arm
-- is dead-but-unproven; for `LitChar` it is the normal case). The wildcard is
-- load-bearing: without it GHC inserts a `patError` bottom.
classify :: Char -> Int
classify 'a' = 1
classify 'b' = 2
classify _   = 0

{- @lean
theorem letterA_val : letterA = 'A' := by rfl
-}

{- @lean
theorem accent_val : accent = 'é' := by rfl
-}

{- @lean
theorem arabicFive_val : arabicFive = '٥' := by rfl
-}

{- @lean
theorem sameChar_refl : sameChar letterA letterA = true := by blaster
-}

{- @lean
theorem sameChar_sym : ∀ (a b : Char), sameChar a b = sameChar b a := by blaster
-}

{- @lean
theorem charLess_digit_letter : charLess digitZero letterA = true := by blaster
-}

{- @lean
theorem charLE_refl : ∀ (c : Char), charLE c c = true := by blaster
-}

{- @lean
theorem ord_letterA : charCode letterA = 65 := by rfl
-}

{- @lean
theorem ord_digitZero : charCode digitZero = 48 := by rfl
-}

-- ROUND-TRIP, `Nat → Char → Nat`, with the explicit precondition that keeps `n`
-- out of the surrogate range. `n < 128` is the shape blaster verifies (plan
-- correction 6); a bound stated as an explicit non-surrogate disjunction forces
-- `Char`'s `val : UInt32` representation, which blaster cannot encode.
{- @lean
theorem ord_ofNat_roundtrip : ∀ (n : Nat), n < 128 → charCode (Char.ofNat n) = (n : Int) := by
  blaster
-}

-- SEMANTIC PINS for `isDigit`, both ends of the ASCII digit range and both
-- letter cases, plus the Unicode digit that is `False` in Haskell and `false`
-- in Lean — the agreement that makes this the only mappable predicate.
{- @lean
theorem digitP_0 : digitP '0' = true := by rfl
-}

{- @lean
theorem digitP_9 : digitP '9' = true := by rfl
-}

{- @lean
theorem digitP_a : digitP 'a' = false := by rfl
-}

{- @lean
theorem digitP_A : digitP 'A' = false := by rfl
-}

{- @lean
theorem digitP_arabicFive : digitP arabicFive = false := by rfl
-}

{- @lean
theorem classify_a : classify 'a' = 1 := by rfl
-}

{- @lean
theorem classify_b : classify 'b' = 2 := by rfl
-}

{- @lean
theorem classify_other : classify 'z' = 0 := by rfl
-}
