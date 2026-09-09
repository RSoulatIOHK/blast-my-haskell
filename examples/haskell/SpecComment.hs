{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module SpecComment where

-- M4 TASK 3, SECOND PASS — REGRESSION FIXTURE for the COMMENT half of the
-- literal-aware scan. Spec text is copied VERBATIM into the generated Lean
-- (`shim/spec-plugin/GhcSpecDump.hs` lexes with `rawTokStream = True` and keeps
-- the comment body uninterpreted), so a LEAN comment a user writes inside an
-- `@lean` block reaches the ctor-qualification pass as plain text. Measured at
-- the parent commit (37140d0): a comment carrying an ODD number of `"` opened a
-- spurious literal that closed on the OPENING quote of the next REAL literal,
-- putting that literal's CONTENTS in a CODE segment — `"Point (1)"` came out
-- `"Point.Point (1)"`. Silent inside `resolveSpecText`; loud here only because
-- every theorem below compares the literal against something independent of it.
--
-- Ordinary Haskell throughout. The comments under test are LEAN comments inside
-- the spec blocks, not the Haskell comments that delimit them.

data Point = Point Int Int

label :: String
label = "Point (1)"

dashes :: String
dashes = "-- not a comment"

mkPoint :: Int -> Int -> Point
mkPoint x y = Point x y

px :: Point -> Int
px (Point x _) = x

-- (1) A `--` comment with ONE quote, then a real literal that must survive
-- verbatim AND a ctor application that must still be qualified.
{- @lean
-- the label is "Point (1) — one quote, deliberately unbalanced
theorem label_after_line_comment :
    (label, mkPoint 1 2) = ("Point (1)".toList, Point 1 2) := by rfl
-}

-- (2) The same hazard in a Lean BLOCK comment.
{- @lean
/- note: "Point -/
theorem label_after_block_comment : ("Point (1)".toList).length = 9 := by rfl
-}

-- (3) NESTED Lean block comments (Lean nests them): the inner opener pushes, the
-- first closer pops to depth 1, and only the second closes the comment.
{- @lean
/- outer /- inner "Point -/ -/
theorem label_after_nested_comment : label = "Point (1)".toList := by rfl
-}

-- (4) The other direction, which a comment-first scanner gets wrong: `--` inside
-- a STRING LITERAL does not start a comment, so the rest of the line is code.
{- @lean
theorem dashes_val : dashes = "-- not a comment".toList := by rfl
-}

-- (5) A single `-` or `/` is not a comment opener — subtraction and division in
-- code position, with a ctor application beside them.
{- @lean
theorem arith_is_not_a_comment :
    ((7 - 1) / 2, px (mkPoint 1 2)) = ((3 : Int), 1) := by rfl
-}
