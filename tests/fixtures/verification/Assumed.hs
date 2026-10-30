module Assumed where
value :: Bool
value = True
{- @lean
axiom assumption : value = false
theorem conditional : value = false := assumption
-}
