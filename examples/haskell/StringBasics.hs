{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module StringBasics where

greeting :: String
greeting = "hi"

quoted :: String
quoted = "say \"hi\"\n"
