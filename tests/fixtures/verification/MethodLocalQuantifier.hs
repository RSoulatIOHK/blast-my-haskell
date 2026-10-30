{-# LANGUAGE RankNTypes #-}
module MethodLocalQuantifier where

class C a where
  probe :: forall b. Eq b => a -> b -> Bool
  probe _ x = x == x

data T = T
instance C T
