{-# LANGUAGE TemplateHaskell #-}

-- | A declaration quasi-quoter for embedding Lean property text in Haskell.
-- Usage (top level): @[lean| theorem foo : … := by blaster |]@.
-- At compile time it records the raw text to @$LEAN_SPEC_DIR/<Module>/<line>.lean@
-- and expands to no declarations. Outside the transpile sandbox (no
-- @LEAN_SPEC_DIR@) it is a no-op.
module Lean.Spec (lean) where

import Language.Haskell.TH (Dec, Loc (..), Q, location, runIO)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)
import System.FilePath ((</>))

lean :: QuasiQuoter
lean =
  QuasiQuoter
    { quoteExp  = \_ -> fail "lean: use [lean| … |] only at top level (declaration position)"
    , quotePat  = \_ -> fail "lean: declaration-only quasi-quoter"
    , quoteType = \_ -> fail "lean: declaration-only quasi-quoter"
    , quoteDec  = leanDec
    }

leanDec :: String -> Q [Dec]
leanDec txt = do
  loc <- location
  let modName   = loc_module loc
      startLine = fst (loc_start loc)   -- the `[lean|` line
      endLine   = fst (loc_end loc)     -- the `|]` line
  runIO $ do
    mdir <- lookupEnv "LEAN_SPEC_DIR"
    case mdir of
      Nothing  -> pure ()
      Just dir -> do
        let d = dir </> modName
        createDirectoryIfMissing True d
        -- Filename encodes the full source-span lines so the transpiler can
        -- build the map's `hs` range (opener..closer) for the squiggle.
        writeFile (d </> (show startLine ++ "-" ++ show endLine ++ ".lean")) txt
  pure []
