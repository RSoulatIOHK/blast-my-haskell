module Refuted where
value :: Bool
value = True
{- @lean
theorem wrong : value = false := by blaster
-}
