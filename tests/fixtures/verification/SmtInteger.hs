module SmtInteger where
inc :: Integer -> Integer
inc x = x + 1
{- @lean
theorem inc_value : ∀ (x : Int), inc x = x + 1 := by blaster
-}
