{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module StringCtorClash where

-- M4 TASK 3's REGRESSION FIXTURE. A data type whose CONSTRUCTOR NAME also occurs
-- inside string literals — the shape that made the transpiler's textual
-- ctor-qualification pass silently wrong once M4 Task 2 let real literal bytes
-- reach the emitter. Measured at the parent commit (3664d3f): every literal
-- below came out with `Point.Point` spliced into its TEXT, and both the
-- transpile and `lake build` of the result exited 0. The theorems at the bottom
-- are the loud pins; the fix is `Emit.mapOutsideLiterals`.
--
-- Ordinary Haskell throughout: nothing here is a transpiler-specific trick, so
-- the fixture is also a plain string/record fixture.

data Point = Point Int Int

-- (1) The plain hazard: a literal that spells an application of `Point`.
label :: String
label = "Point (1)"

-- (2) The ctor name adjacent to a `\"` escape on both sides. A scanner that
-- merely counts quotes ends the literal at the first inner one and rewrites the
-- rest of the line as if it were code.
quotedLabel :: String
quotedLabel = "\"Point (1)\""

-- (3) A literal ENDING in a backslash. A scanner that skips the character after
-- every backslash without tracking that the backslash was itself escaped reads
-- the closing quote as `\"` and never leaves the literal.
trailingBackslash :: String
trailingBackslash = "Point (1)\\"

-- (4) All four of `resolveUserCtors`' fixed needles at once, inside one literal:
-- `| Point ` (alt pattern), `(Point)`, ` Point (` and `(Point (`.
needles :: String
needles = "| Point y (Point) x Point (1) (Point (1))"

-- (5) A literal followed by more code in the SAME body — the scanner has to
-- resume, or the `Point` application after it is left unqualified.
labelled :: Int -> (String, Point)
labelled n = ("Point (1)", Point n n)

mkPoint :: Int -> Int -> Point
mkPoint x y = Point x y

px :: Point -> Int
px (Point x _) = x

{- @lean
theorem label_val : label = ['P', 'o', 'i', 'n', 't', ' ', '(', '1', ')'] := by rfl
-}

{- @lean
theorem label_len : label.length = 9 := by rfl
-}

{- @lean
theorem quotedLabel_len : quotedLabel.length = 11 := by rfl
-}

{- @lean
theorem trailingBackslash_len : trailingBackslash.length = 10 := by rfl
-}

{- @lean
theorem needles_len : needles.length = 41 := by rfl
-}

{- @lean
theorem labelled_snd : labelled 7 = (label, Point 7 7) := by rfl
-}

-- BOTH DIRECTIONS IN ONE THEOREM, on hand-written text (the residual risk the
-- old hedge comment described, now a guard): the literal must survive verbatim
-- — a rewrite makes it 15 characters and this fails — while the `Point 1 2`
-- immediately after it must still be qualified, or it does not elaborate at all
-- ("function expected at Point").
{- @lean
theorem label_then_ctor : (label, mkPoint 1 2) = ("Point (1)".toList, Point 1 2) := by rfl
-}

-- The two escape boundaries in hand-written theorem text, each followed by code
-- that needs the rewrite.
{- @lean
theorem esc_then_ctor : ("\"Point (1)\"".toList, px (Point 3 4)) = (quotedLabel, 3) := by rfl
-}

{- @lean
theorem backslash_then_ctor : ("Point (1)\\".toList, px (Point 5 6)) = (trailingBackslash, 5) := by rfl
-}
