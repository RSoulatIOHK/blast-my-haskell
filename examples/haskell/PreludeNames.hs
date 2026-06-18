{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module PreludeNames where
    import Prelude
    probe :: [Int] -> [Int] -> ([Int], Int, Bool)
    probe xs ys =
      ( map (\x -> x + 1) (filter (\x -> x > 0) (reverse (xs ++ ys)))
      , foldr (+) 0 xs + foldl (+) 0 ys + length xs
      , (not (null xs) && otherwise) || const True (flip (-) 1 0) )
