{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module StringBasics where

greeting :: String
greeting = "hi"

-- HAZARDOUS for the emitter, not for Haskell: a quote, a backslash escape and a
-- newline. Before M4 Task 2 escaped literals this emitted `("say "hi"` + a raw
-- newline, i.e. a Lean SYNTAX error.
quoted :: String
quoted = "say \"hi\"\n"

-- A literal that is exactly one double quote, and one that is exactly one
-- backslash: the two single-character hazards.
justQuote :: String
justQuote = "\""

justBackslash :: String
justBackslash = "\\"

-- Non-ASCII: GHC spells this one with `unpackCStringUtf8#`, not
-- `unpackCString#` (measured — the plain unpacker is used only for pure ASCII).
accented :: String
accented = "caf\233"

-- NUL is FAITHFUL, 3 characters. GHC encodes it as modified UTF-8's overlong
-- `C0 80`, which a standard-UTF-8 decoder rejects; the shim decodes it back to a
-- real U+0000 because that is a legal Lean `Char`. Only lone surrogates are
-- refused — see the must-fail `StringSurrogate.hs`.
withNul :: String
withNul = "a\0b"

shout :: String -> String
shout s = s ++ "!"

nameLen :: String -> Int
nameLen s = length s

{- @lean
theorem greeting_val : greeting = ['h', 'i'] := by rfl
-}

{- @lean
theorem quoted_val : quoted = ['s', 'a', 'y', ' ', '"', 'h', 'i', '"', '\n'] := by rfl
-}

{- @lean
theorem quoted_len : nameLen quoted = 9 := by rfl
-}

{- @lean
theorem justQuote_val : justQuote = ['"'] := by rfl
-}

{- @lean
theorem justBackslash_val : justBackslash = ['\\'] := by rfl
-}

{- @lean
theorem accented_val : accented = ['c', 'a', 'f', 'é'] := by rfl
-}

{- @lean
theorem withNul_val : withNul = ['a', '\x00', 'b'] := by rfl
-}

{- @lean
theorem withNul_len : nameLen withNul = 3 := by rfl
-}

{- @lean
theorem shout_greeting : shout greeting = ['h', 'i', '!'] := by rfl
-}

{- @lean
theorem shout_len : ∀ (cs : List Char), nameLen (shout cs) = nameLen cs + 1 := by
  simp [shout, nameLen]
-}
