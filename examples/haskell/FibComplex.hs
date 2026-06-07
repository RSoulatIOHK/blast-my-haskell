{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module FibComplex where

-- A semantically-equivalent fib that stresses more Haskell surface:
--   * multiple pattern equations (0, 1, 2, 3 as explicit literal patterns)
--   * a guard with `otherwise`
--   * an inequality comparison (n <= 5)
--   * a `where`-bound auxiliary that itself recurses
--   * a local `let` binding two shared sub-expressions
--   * an algebraic identity: fib n = 2 * fib (n-2) + fib (n-3)  (for n >= 3)
--
-- All branches still return the standard fibonacci number with fib 0 = fib 1 = 1.
fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib 2 = 2
fib 3 = 3
fib n
  | n <= 5    = standardFib n
  | otherwise = let prev2 = fib (n - 2)
                    prev3 = fib (n - 3)
                in 2 * prev2 + prev3
  where
    standardFib k = fib (k - 1) + fib (k - 2)

{- @lean
#blaster [ fib 0 = 1 ]
#blaster [ fib 6 = 13 ]

theorem correct_fib : ∀ (n : Int), n > 0 →
    fib n = if n ≤ 1 then 1 else fib (n - 2) + fib (n - 1) := by
  intro n
  induction n <;> blaster (timeout: 10)
-}
