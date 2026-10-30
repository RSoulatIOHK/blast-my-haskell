module ImportClient where

import qualified ImportBase

fromBase :: Integer -> Integer
fromBase x = ImportBase.scale x + ImportBase.offset

belowBase :: Integer -> Bool
belowBase x = x < ImportBase.offset
