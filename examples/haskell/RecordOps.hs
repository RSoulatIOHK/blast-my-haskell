{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module RecordOps where

data Point = Point { px :: Int, py :: Int }

data Rect = Rect { topLeft :: Point, width :: Int, height :: Int }

mkPoint :: Int -> Int -> Point
mkPoint x y = Point { px = x, py = y }

shiftX :: Int -> Point -> Point
shiftX d p = p { px = px p + d }

resize :: Int -> Int -> Rect -> Rect
resize w h r = r { width = w, height = h }

xs :: [Point] -> [Int]
xs ps = map px ps

area :: Rect -> Int
area r = width r * height r

{- @lean
theorem mkPoint_px : ∀ (x y : Int), px (mkPoint x y) = x := by blaster
-}

{- @lean
theorem shiftX_moves : ∀ (d x y : Int), px (shiftX d (mkPoint x y)) = x + d := by blaster
-}

{- @lean
theorem shiftX_keeps_py : ∀ (d x y : Int), py (shiftX d (mkPoint x y)) = y := by blaster
-}

{- @lean
theorem resize_area : ∀ (w h : Int), area (resize w h (Rect (Point 0 0) 1 1)) = w * h := by blaster
-}

{- @lean
theorem xs_example : xs [mkPoint 1 2, mkPoint 3 4] = [1, 3] := by decide
-}
