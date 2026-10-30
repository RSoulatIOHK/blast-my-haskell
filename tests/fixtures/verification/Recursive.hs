module Recursive where
walk :: Integer -> Integer
walk n = if n <= 0 then 0 else walk (n - 1)
{- @lean
-- Even a reflexive theorem has the recursive definition in its type, and its
-- admitted termination obligation must be found transitively by the audit.
theorem walk_self : walk 2 = walk 2 := by rfl
-}
