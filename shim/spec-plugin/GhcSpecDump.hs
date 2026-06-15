{-# LANGUAGE LambdaCase #-}
module GhcSpecDump (plugin) where

import Data.Char        (isSpace)
import Data.List        (stripPrefix)
import Data.Maybe       (mapMaybe)
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)
import System.FilePath  ((</>))

import GHC.Plugins
import GHC.Parser.Lexer    (lexTokenStream, ParseResult(..), mkParserOpts, Token(..))
import GHC.Types.SrcLoc

plugin :: Plugin
plugin = defaultPlugin
  { pluginRecompile    = purePlugin
  , parsedResultAction = \_ ms pm -> do
      dflags <- getDynFlags
      liftIO (dumpSpecs dflags ms)
      pure pm
  }

dumpSpecs :: DynFlags -> ModSummary -> IO ()
dumpSpecs dflags ms =
  lookupEnv "LEAN_SPEC_DIR" >>= \case
    Nothing  -> pure ()
    Just dir -> case ms_hspp_buf ms of
      Nothing  -> pure ()
      Just buf -> do
        let modName = moduleNameString (moduleName (ms_mod ms))
            loc     = mkRealSrcLoc (mkFastString (ms_hspp_file ms)) 1 1
            -- mkParserOpts warningFlags extensionFlags
            --              safeImports isHaddock rawTokStream usePosPrags
            -- rawTokStream = True retains comment tokens in the stream.
            popts   = mkParserOpts (warningFlags dflags) (extensionFlags dflags)
                                   False True True False
        case lexTokenStream popts buf loc of
          POk _ toks -> mapM_ (writeSpec dir modName) (mapMaybe leanComment toks)
          PFailed _  -> pure ()

leanComment :: Located Token -> Maybe (Int, Int, String)
leanComment (L sp tok) = case tok of
  ITblockComment s _ -> do
    rest <- stripPrefix "@lean" (dropWhile isSpace (stripBlock s))
    case sp of
      RealSrcSpan r _ -> Just (srcSpanStartLine r, srcSpanEndLine r, trim rest)
      _               -> Nothing
  _ -> Nothing

-- | Strip the surrounding @{- … -}@ delimiters from a block-comment lexeme.
stripBlock :: String -> String
stripBlock s0 =
  let s1 = maybe s0 id (stripPrefix "{-" s0)
  in reverse (maybe (reverse s1) id (stripPrefix "}-" (reverse s1)))

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace

writeSpec :: FilePath -> String -> (Int, Int, String) -> IO ()
writeSpec dir modName (s, e, txt) = do
  let d = dir </> modName
  createDirectoryIfMissing True d
  writeFile (d </> (show s ++ "-" ++ show e ++ ".lean")) txt
