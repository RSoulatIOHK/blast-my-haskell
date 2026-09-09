{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module SpecInterp where

-- MUST-FAIL FIXTURE (M4 gate review). An ORDINARY `@lean` spec block that uses
-- Lean's string INTERPOLATION (`s!"…"`), which is one of the three lexical forms
-- the ctor-rewrite scanner (`Emit.litSegments`) does not model. On such a block
-- the scanner desyncs in the SILENT direction: the interpolation's outer literal
-- is closed by the nested literal's opening quote, so the next real literal's
-- CONTENT lands in a code segment and a constructor name inside it is rewritten.
--
-- MEASURED at the parent (`6bb139e`), through `resolveSpecText`:
--   in : theorem t : x = s!"{f "Point (1)"}"
--   out: theorem t : x = s!"{f "Point.Point (1)"}"
-- The theorem elaborates and proves a property of a string nobody wrote — the
-- one failure mode this project forbids. So the module is REFUSED by name:
--
--   error: spec text uses a lexical form the constructor rewrite cannot scan:
--   string interpolation (`s!"…"`)
--
-- Transpilation exits nonzero and writes no `.lean`. The other two forms (a raw
-- string `r"…"`, a guillemet identifier `«…»`) are refused by the same check;
-- they are pinned as `#guard`s in `Tests/Unit.lean` rather than as three
-- fixtures, since the refusal is one code path.
--
-- THE REMEDY, for a reader who lands here from the error: state the property
-- without the interpolation (`theorem t : describe = label ++ [' ', 'o', 'k']`).

data Point = Point Int Int

label :: String
label = "Point (1)"

describe :: String
describe = label ++ " ok"

mkPoint :: Int -> Int -> Point
mkPoint x y = Point x y

{- @lean
theorem describe_val : describe = s!"{label} ok".toList := by rfl
-}
