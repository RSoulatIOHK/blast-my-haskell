{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module LocalRec where
    import Prelude

    -- `go` recurses on the list spine (structurally decreasing), which Lean's
    -- `let rec` accepts directly.
    sumList :: [Int] -> Int
    sumList xs = go xs 0
      where
        go []     acc = acc
        go (y:ys) acc = go ys (acc + y)
