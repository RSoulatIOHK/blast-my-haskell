{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module TupleTriple where

triple :: Int -> Int -> Int -> (Int, Int, Int)
triple a b c = (a, b, c)

sumTriple :: (Int, Int, Int) -> Int
sumTriple (a, b, c) = a + b + c

rotate :: (Int, Int, Int) -> (Int, Int, Int)
rotate (a, b, c) = (b, c, a)

quad :: Int -> Int -> Int -> Int -> (Int, Int, Int, Int)
quad a b c d = (a, b, c, d)

fourth :: (Int, Int, Int, Int) -> Int
fourth (_, _, _, d) = d

firstOfTriple :: (Int, Int, Int) -> Int
firstOfTriple (a, _, _) = a

{- @lean
theorem sumTriple_triple :
    ∀ (a b c : Int), sumTriple (triple a b c) = a + b + c := by blaster
-}

{- @lean
theorem rotate_sum :
    ∀ (a b c : Int), sumTriple (rotate (triple a b c)) = a + b + c := by blaster
-}

{- @lean
theorem fourth_quad :
    ∀ (a b c d : Int), fourth (quad a b c d) = d := by blaster
-}

{- @lean
theorem firstOfTriple_triple :
    ∀ (a b c : Int), firstOfTriple (triple a b c) = a := by blaster
-}
