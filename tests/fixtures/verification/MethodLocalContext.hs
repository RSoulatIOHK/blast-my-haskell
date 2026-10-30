{-# LANGUAGE ConstrainedClassMethods #-}
module MethodLocalContext where

class C a where
  probe :: Eq a => a -> Bool
  probe x = x == x
