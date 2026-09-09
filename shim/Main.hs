{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import qualified Data.ByteString.Lazy        as BSL
import qualified Data.ByteString.Lazy.Char8  as BSLC
import qualified Data.Aeson                  as A
import           Data.Aeson                  (Value, object, (.=))
import qualified Data.Aeson.Encode.Pretty    as AP
import qualified Data.Aeson.KeyMap           as AKM
import qualified Data.Map.Strict             as Map
import           Data.Map.Strict             (Map)
import qualified Data.Text                   as T
import           Data.Text.Encoding          (decodeUtf8With, encodeUtf8)
import           Data.Text.Encoding.Error    (lenientDecode)
import qualified Data.ByteString             as BS
import           Data.Word                   (Word8)
import           Data.Char                   (ord, toUpper)
import           Numeric                     (showHex)
import           System.Environment          (getArgs)
import           System.Exit                 (die)
import qualified Codec.Serialise             as Ser

import           GhcDump.Ast

------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------

readSModuleFile :: FilePath -> IO SModule
readSModuleFile path = Ser.deserialise <$> BSL.readFile path

main :: IO ()
main = do
  args <- getArgs
  case args of
    [cborPath] -> emit cborPath Nothing
    [cborPath, "--decls", declsPath] -> emit cborPath (Just declsPath)
    _ -> die "usage: ghc-core-shim <Module.passNNNN.cbor> [--decls <Module.decls.json>]"

-- | Read the Core dump, optionally splice in the type/instance decl shapes
-- from the decl-plugin, and emit the unified JSON to stdout.
emit :: FilePath -> Maybe FilePath -> IO ()
emit cborPath mDeclsPath = do
  m <- readSModuleFile cborPath
  let env     = collectBinders m
      modName = getModuleName (moduleName m)
      coreVal = convertModule env modName m
  decls <- case mDeclsPath of
    Nothing -> pure A.Null
    Just p  -> do
      bs <- BSL.readFile p
      case A.decode bs :: Maybe A.Value of
        Just v  -> pure v
        Nothing -> die ("could not parse " <> p)
  let merged = mergeDecls coreVal decls
  BSLC.putStrLn (AP.encodePretty merged)

-- | Splice `typeDecls`, `instances` and `classDecls` from the decl-plugin's JSON
-- into the core-side JSON. If decls is Null (no plugin output), pass core
-- through. A key the plugin did not write becomes `A.Null`, which the Lean
-- parser reads as the empty list — so an OLD decls.json (pre-`classDecls`
-- plugin) still parses.
mergeDecls :: A.Value -> A.Value -> A.Value
mergeDecls core decls =
  case (core, decls) of
    (A.Object cobj, A.Object dobj) ->
      let pick k = maybe A.Null id (AKM.lookup k dobj)
          coreWith = AKM.insert "typeDecls"  (pick "typeDecls")
                   $ AKM.insert "instances"  (pick "instances")
                   $ AKM.insert "classDecls" (pick "classDecls")
                   $ cobj
      in A.Object coreWith
    _ -> core

------------------------------------------------------------------------
-- Env: BinderId → SBinder
------------------------------------------------------------------------

type Env = Map BinderId SBinder

collectBinders :: SModule -> Env
collectBinders m = foldr addTopBinding Map.empty (moduleTopBindings m)

addTopBinding :: STopBinding -> Env -> Env
addTopBinding tb env = case tb of
  NonRecTopBinding b _ rhs -> addExpr rhs (addBinder b env)
  RecTopBinding pairs ->
    let env' = foldr (\(b, _, _) -> addBinder b) env pairs
    in foldr (\(_, _, rhs) -> addExpr rhs) env' pairs

addBinder :: SBinder -> Env -> Env
addBinder sb@(SBndr b) env = Map.insert (binderId b) sb env

addExpr :: SExpr -> Env -> Env
addExpr e env = case e of
  EVar _ -> env
  EVarGlobal _ -> env
  ELit _ -> env
  EApp f a -> addExpr f (addExpr a env)
  ETyLam b body -> addBinder b (addExpr body env)
  ELam b body -> addBinder b (addExpr body env)
  ELet pairs body ->
    let env' = foldr (\(b, _) -> addBinder b) env pairs
    in foldr (\(_, rhs) -> addExpr rhs) (addExpr body env') pairs
  ECase scr b alts ->
    let env' = addBinder b (addExpr scr env)
    in foldr addAlt env' alts
  ETick _ x -> addExpr x env
  EType _ -> env
  ECoercion -> env

addAlt :: SAlt -> Env -> Env
addAlt (Alt _ bndrs rhs) env =
  let env' = foldr addBinder env bndrs
  in addExpr rhs env'

------------------------------------------------------------------------
-- Module → JSON
------------------------------------------------------------------------

convertModule :: Env -> T.Text -> SModule -> Value
convertModule env modName m = object
  [ "binds" .= map (convertTopBinding env modName) (moduleTopBindings m) ]

convertTopBinding :: Env -> T.Text -> STopBinding -> Value
convertTopBinding env modName = \case
  NonRecTopBinding b _ rhs -> object
    [ "tag"    .= ("NonRec" :: T.Text)
    , "binder" .= convertSBinder b
    , "rhs"    .= convertExpr env modName rhs
    ]
  RecTopBinding pairs -> object
    [ "tag"   .= ("Rec" :: T.Text)
    , "pairs" .= [ object [ "binder" .= convertSBinder b
                          , "rhs"    .= convertExpr env modName rhs ]
                 | (b, _, rhs) <- pairs ]
    ]

------------------------------------------------------------------------
-- Binders
------------------------------------------------------------------------

convertSBinder :: SBinder -> Value
convertSBinder (SBndr b) = object
  [ "name"   .= binderName b
  , "unique" .= binderUniqueAsNat b
  , "type"   .= convertBinderType b
  , "role"   .= binderRole b
  ]

binderUniqueAsNat :: Binder' SBinder BinderId -> Int
binderUniqueAsNat b =
  let BinderId (Unique _ n) = binderId b in n

convertBinderType :: Binder' SBinder BinderId -> Value
convertBinderType (Binder { binderType = t }) = convertType t
convertBinderType (TyBinder { binderKind = k }) = convertType k

binderRole :: Binder' SBinder BinderId -> T.Text
binderRole (TyBinder {}) = "tyVar"
binderRole b@(Binder {}) =
  case binderIdDetails b of
    DFunId -> "dict"
    _      ->
      let n = T.unpack (binderName b)
      -- `$dm<method>` is a class DEFAULT-METHOD body, not a dictionary. The
      -- consumer erases dict-role Vars in argument position (Lower.lean), so
      -- classifying `$dmgreet` as a dict would silently delete the default's
      -- body wherever it is passed as an argument. The exemption is exact, not a
      -- guess: a dictionary's name is `$d` + a CLASS name, which is always
      -- upper-case (`$dGreet`, `$dIP`), while `$dm` is followed by a METHOD
      -- name, always lower-case or symbolic — the two prefixes cannot collide.
      in if take 3 n == "$dm" then "id"
         else if take 2 n `elem` ["$d", "$f"] then "dict" else "id"

------------------------------------------------------------------------
-- Expr
------------------------------------------------------------------------

convertExpr :: Env -> T.Text -> SExpr -> Value
convertExpr env modName = go
  where
    go = \case
      EVar bid ->
        let v = case Map.lookup bid env of
                  Just sb -> convertSBinder sb
                  Nothing ->
                    let BinderId (Unique _ n) = bid
                    in object [ "name" .= ("<unresolved>" :: T.Text)
                              , "unique" .= n
                              , "type" .= unknownType
                              , "role" .= ("id" :: T.Text) ]
        in object [ "tag" .= ("Var" :: T.Text), "var" .= v ]
      EVarGlobal en ->
        object [ "tag" .= ("Var" :: T.Text)
               , "var" .= convertExternalName modName en ]
      ELit l -> object [ "tag" .= ("Lit" :: T.Text), "lit" .= convertLit l ]
      EApp f a -> object [ "tag" .= ("App" :: T.Text)
                         , "fun" .= go f
                         , "arg" .= go a ]
      ETyLam b body -> object [ "tag"    .= ("Lam" :: T.Text)
                              , "binder" .= convertSBinder (forceTyVar b)
                              , "body"   .= go body ]
      ELam b body -> object [ "tag"    .= ("Lam" :: T.Text)
                            , "binder" .= convertSBinder b
                            , "body"   .= go body ]
      ELet pairs body -> object [ "tag"  .= ("Let" :: T.Text)
                                , "bind" .= letBinds pairs
                                , "body" .= go body ]
      ECase scr b alts -> object [ "tag"       .= ("Case" :: T.Text)
                                 , "scrutinee" .= go scr
                                 , "binder"    .= convertSBinder b
                                 , "type"      .= unknownType
                                 , "alts"      .= map (convertAlt env modName) alts ]
      ETick _ x -> object [ "tag" .= ("Tick" :: T.Text), "expr" .= go x ]
      EType t -> object [ "tag" .= ("Type" :: T.Text), "type" .= convertType t ]
      -- A coercion in expression position. ghc-dump has no `ECast` node at all
      -- (`Convert.hs`: `Cast x _ -> cvtExpr x` erases the cast), so this is the
      -- only coercion the shim can ever see. It carries no payload: the Lean
      -- side only needs a token it can erase in argument position. The former
      -- `{"tag":"Cast","expr":{}}` encoding was unparseable (Parse.lean tried to
      -- parse the empty `expr` and aborted).
      ECoercion -> object [ "tag" .= ("Coercion" :: T.Text) ]

    letBinds [(b, rhs)] = object
      [ "tag"    .= ("NonRec" :: T.Text)
      , "binder" .= convertSBinder b
      , "rhs"    .= go rhs ]
    letBinds pairs = object
      [ "tag"   .= ("Rec" :: T.Text)
      , "pairs" .= [ object [ "binder" .= convertSBinder b
                            , "rhs"    .= go rhs ]
                   | (b, rhs) <- pairs ] ]

forceTyVar :: SBinder -> SBinder
forceTyVar sb@(SBndr (TyBinder{})) = sb
forceTyVar (SBndr b@(Binder{})) = SBndr (TyBinder { binderName = binderName b
                                                  , binderId   = binderId b
                                                  , binderKind = binderType b })

convertAlt :: Env -> T.Text -> SAlt -> Value
convertAlt env modName (Alt con bndrs rhs) = object
  [ "con"     .= convertAltCon con
  , "binders" .= map convertSBinder bndrs
  , "rhs"     .= convertExpr env modName rhs
  ]

convertAltCon :: AltCon -> Value
convertAltCon = \case
  AltDataCon n -> object [ "tag" .= ("DataAlt" :: T.Text), "name" .= n ]
  AltLit l     -> object [ "tag" .= ("LitAlt"  :: T.Text), "lit"  .= convertLit l ]
  AltDefault   -> object [ "tag" .= ("DEFAULT" :: T.Text) ]

------------------------------------------------------------------------
-- External names: strip the *current* module's prefix; keep prefix for
-- cross-module refs so Maps can resolve them (`GHC.Num.+`, etc.).
------------------------------------------------------------------------

convertExternalName :: T.Text -> ExternalName -> Value
convertExternalName _ ForeignCall = object
  [ "name"   .= ("<foreigncall>" :: T.Text)
  , "unique" .= (0 :: Int)
  , "type"   .= unknownType
  , "role"   .= ("id" :: T.Text)
  ]
convertExternalName modName (ExternalName mn nm (Unique _ u)) =
  let other = getModuleName mn
      name = if other == modName then nm
             else other <> "." <> nm
      -- Heuristic for dict instances exported from GHC libraries: names
      -- start with `$f` (instance methods) or `$d` (instance dicts).
      --
      -- `$dm` is exempted here for the same reason as in `binderRole` (see the
      -- argument there), and the exemption is needed in BOTH places because this
      -- is an INDEPENDENT copy of the rule — and the one that classifies a
      -- *reference*. GHC reaches a top-level name through `EVarGlobal` even
      -- inside the defining module, so every `$dm<method>` USE lands in this
      -- function while only its binder goes through `binderRole`. With the
      -- exemption in one place only, a bind said `id` and its own reference said
      -- `dict` (observed in the DefaultMethods dump: binder at `/binds/4`,
      -- reference at `/binds/26/pairs/1/rhs/fun/fun`) — and a dict-role
      -- reference in argument position is ERASED by the consumer's `Lower`.
      --
      -- Tested on `nm`, the BARE name, not on `name`: a cross-module reference
      -- is prefixed (`GHC.Show.$dmshowList`), which a `take 3` would miss.
      role = if T.take 3 nm == "$dm" then "id"
             else if T.take 2 nm `elem` ["$d", "$f"] then "dict" else "id"
  in object [ "name"   .= name
            , "unique" .= u
            , "type"   .= unknownType
            , "role"   .= (role :: T.Text) ]

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

convertType :: SType -> Value
convertType = \case
  VarTy (BinderId (Unique _ n)) ->
    object [ "tag" .= ("TyVar" :: T.Text), "name" .= ("_v" <> T.pack (show n)) ]
  FunTy a r -> object [ "tag" .= ("TyFun" :: T.Text)
                      , "arg" .= convertType a
                      , "res" .= convertType r ]
  TyConApp (TyCon name _) args -> object [ "tag"  .= ("TyCon" :: T.Text)
                                         , "name" .= name
                                         , "args" .= map convertType args ]
  AppTy f a -> object [ "tag" .= ("TyApp" :: T.Text)
                      , "fun" .= convertType f
                      , "arg" .= convertType a ]
  ForAllTy (SBndr b) body ->
    object [ "tag"  .= ("ForAll" :: T.Text)
           , "var"  .= binderName b
           , "body" .= convertType body ]
  LitTy               -> unknownType
  CoercionTy          -> unknownType

unknownType :: Value
unknownType = object [ "tag"  .= ("TyCon" :: T.Text)
                     , "name" .= ("_Unknown" :: T.Text)
                     , "args" .= ([] :: [Value]) ]

------------------------------------------------------------------------
-- Literals
------------------------------------------------------------------------

convertLit :: Lit -> Value
convertLit = \case
  -- M4 TASK 4. This arm was the LAST silent lossy one, and it was invisible for
  -- the project's whole life because no dump had ever contained a `LitChar`:
  -- `T.singleton` is not `Text`'s identity on `Char`. `text-1.2.5.0` applies
  -- `safe`, which maps every surrogate to U+FFFD, so `T.singleton '\55296'`
  -- (and `'\57343'`) is the REPLACEMENT CHARACTER — measured under GHC 9.2.7.
  -- A Haskell `Char` spans [0,0x10FFFF] INCLUDING the 2048 surrogates and a Lean
  -- `Char` excludes them, so such a literal has no Lean value at all; emitting
  -- U+FFFD would give it a DIFFERENT, perfectly legal one, and compile.
  -- (Measured pre-fix: `CharSurrogate.hs`'s `lone = '\55296'` emitted
  -- `def lone : Char := '\65533'` with rc=0 and a green `lake build`.)
  --
  -- WHY THE PREDICATE IS NOT `MachStr`'s. The string channel tests
  -- `encodeUtf8 (decodeUtf8With lenientDecode bs) /= bs` on the raw BYTES. Reused
  -- here it would be a guaranteed FALSE NEGATIVE on the only case it exists to
  -- catch: by the time `T.singleton` has run the surrogate is already U+FFFD, and
  -- U+FFFD round-trips UTF-8 perfectly. So the test is on the `Char` ITSELF,
  -- before `Text` can destroy it — the `Lit` carries a real `Char` all the way
  -- from `GhcDump.Convert`, and `Codec.Serialise`'s `Char` instance is the
  -- code point, so the CBOR is lossless and `T.singleton` is the only lossy step.
  -- (Proven by this arm working at all: `U+D800` can only be reported if the
  -- code point survived the dump.)
  --
  -- SCHEMA. The key is `unrepresentable`, the same channel `LitString` uses:
  -- present iff the literal has no faithful Lean image, PRESENCE is the flag and
  -- the content is the evidence the Lean-side refusal names. The CONTENT is
  -- per-tag, and deliberately looks different so the two cannot be misread for
  -- each other: bytes (`"78 ed a0 80 79"`) for `LitString`, whose loss is a
  -- byte-encoding fact, and a code point (`"U+D800"`) for `LitChar`, whose loss
  -- is not — none of the modified-UTF-8/overlong-NUL story applies to a `Char`,
  -- which is why the refusal message is a separate one.
  -- `value` still carries the lossy `T.singleton`: it is what the literal WOULD
  -- have been believed to be, and it is never read, because the flag refuses
  -- first (`Parse.parseLiteral` tests the field before touching `value`).
  --
  -- Flagged, not `die`d, for the same reason as `MachStr`: the shim cannot know
  -- whether a literal reaches emission, so dying here would crash modules whose
  -- only surrogate sits in a dropped bind.
  MachChar c    ->
    object ( [ "tag" .= ("LitChar" :: T.Text), "value" .= T.singleton c ]
          ++ [ "unrepresentable" .= hexCodePoint c | isSurrogate c ] )
  -- `Ast.MachStr` carries the literal's real bytes (strict `BS.ByteString`,
  -- lossless from `GhcDump.Convert`); this arm used to throw them away and emit
  -- the placeholder `"<bs>"`, so EVERY Haskell string literal reached Lean as
  -- the same four characters.
  --
  -- Decoded with a *replacement* decoder, not `decodeUtf8`, because GHC's
  -- payload is MODIFIED UTF-8: measured, `"a\0b"` arrives as `0xC0 0x80` for the
  -- NUL and `"x\55296y"` as a 3-byte encoding of the lone surrogate, neither of
  -- which standard UTF-8 accepts. (Modified UTF-8, NOT CESU-8: a non-BMP
  -- character still gets standard 4-byte UTF-8 — measured, `"\128169"` decodes to
  -- a correct U+1F4A9 — so nothing here may reject non-BMP literals.)
  -- `decodeUtf8` throws on those, which inside `transpile.sh` is a crashed
  -- transpile of an otherwise fine module; lenient decoding yields U+FFFD instead.
  --
  -- M4 TASK 2 SPLIT THE LOSSY CASE IN TWO. Modified UTF-8 deviates from standard
  -- UTF-8 in exactly two places (GHC 9.2.7 `utf8EncodeChar`): the overlong NUL
  -- `C0 80`, and 3-byte encodings of lone surrogates. They have DIFFERENT correct
  -- remedies, so one blanket refusal was the wrong shape:
  --   * U+0000 is a perfectly legal Lean `Char`, so `undoOverlongNul` decodes
  --     `C0 80` back to a real NUL and `"a\0b"` transpiles FAITHFULLY (3 chars).
  --   * U+D800–DFFF does not exist in Lean at all, so it cannot be decoded to
  --     anything — the literal is flagged `unrepresentable` and the Lean side
  --     REFUSES the module (`Emit.unrepresentableStringLiterals`, wired in
  --     `Main.lean`). Flagged, not `die`d: the shim cannot know whether the
  --     literal reaches emission, and dying here would crash modules whose only
  --     such literal sits in a dropped `$tr`/`$cshowsPrec`/error-collapsed bind.
  --
  -- The FLAG PREDICATE is the one audited in the "M4 Task 1" Unit.lean block —
  -- `encodeUtf8 (decodeUtf8With lenientDecode bs) /= bs`, sound in both
  -- directions as a lossiness test — applied to the NUL-repaired bytes, so it now
  -- fires on exactly the residue: lone surrogates and any other byte sequence
  -- that is not valid standard UTF-8. It is still computable ONLY here (the bytes
  -- are gone after JSON), which is why the flag is part of the schema.
  --
  -- SCHEMA. `unrepresentable` is present iff the literal has no faithful Lean
  -- image, and its value is the hex of the ORIGINAL bytes (what GHC actually
  -- produced) so the refusal can name the evidence. `value` still carries the
  -- lenient decode: it is what the U+FFFD-bearing literal WOULD have been
  -- believed to be, and it is never emitted, because the flag refuses first.
  MachStr bs    ->
    let repaired = undoOverlongNul bs
        decoded  = decodeUtf8With lenientDecode repaired
        lossy    = encodeUtf8 decoded /= repaired
    in object ( [ "tag"   .= ("LitString" :: T.Text)
                , "value" .= decoded ]
             ++ [ "unrepresentable" .= hexBytes bs | lossy ] )
  MachNullAddr  -> object [ "tag" .= ("LitInt"    :: T.Text), "value" .= (0 :: Integer) ]
  MachInt n     -> object [ "tag" .= ("LitInt"    :: T.Text), "value" .= n ]
  MachInt64 n   -> object [ "tag" .= ("LitInt"    :: T.Text), "value" .= n ]
  MachWord n    -> object [ "tag" .= ("LitWord"   :: T.Text), "value" .= n ]
  MachWord64 n  -> object [ "tag" .= ("LitWord"   :: T.Text), "value" .= n ]
  MachFloat r   -> object [ "tag" .= ("LitFloat"  :: T.Text), "value" .= (fromRational r :: Double) ]
  MachDouble r  -> object [ "tag" .= ("LitDouble" :: T.Text), "value" .= (fromRational r :: Double) ]
  MachLabel l   -> object [ "tag" .= ("LitLabel"  :: T.Text), "value" .= l ]
  LitInteger n  -> object [ "tag" .= ("LitInt"    :: T.Text), "value" .= n ]
  LitNatural n  -> object [ "tag" .= ("LitWord"   :: T.Text), "value" .= n ]
  LitRubbish    -> object [ "tag" .= ("LitInt"    :: T.Text), "value" .= (0 :: Integer) ]

-- | Decode modified UTF-8's overlong NUL (`C0 80`) back to a real `00` byte.
--
-- Byte-exact and safe to do by a two-byte scan: `0xC0` is not a legal byte
-- ANYWHERE in standard UTF-8 (lead bytes start at `0xC2`, continuation bytes at
-- `0x80`), so it cannot occur inside a valid sequence, and GHC's encoder emits
-- it for nothing but a NUL. The result is therefore standard UTF-8 whenever the
-- original was modified-UTF-8-with-NULs, and is left untouched otherwise.
undoOverlongNul :: BS.ByteString -> BS.ByteString
undoOverlongNul = BS.pack . go . BS.unpack
  where
    go :: [Word8] -> [Word8]
    go (0xC0 : 0x80 : rest) = 0x00 : go rest
    go (b : rest)           = b : go rest
    go []                   = []

-- | Space-separated lowercase hex, for naming the bytes of a literal that has no
-- Lean image (`"x\55296y"` -> `78 ed a0 80 79`).
hexBytes :: BS.ByteString -> T.Text
hexBytes = T.unwords . map (T.pack . pad2 . flip showHex "") . BS.unpack
  where pad2 h = if length h < 2 then '0' : h else h

-- | A lone surrogate: exactly the code points Haskell's `Char` has and Lean's
-- does not. Tested on the `Char`, never on `T.singleton c` (which has already
-- replaced it with U+FFFD) or on encoded bytes (U+FFFD encodes cleanly).
isSurrogate :: Char -> Bool
isSurrogate c = let n = ord c in n >= 0xD800 && n <= 0xDFFF

-- | `U+XXXX`, for naming the code point of a `Char` literal that has no Lean
-- image (`'\55296'` -> `U+D800`). Uppercase with the `U+` prefix so a `LitChar`
-- payload can never be mistaken for `hexBytes`' lowercase byte run — they are
-- different kinds of evidence on the same JSON key.
hexCodePoint :: Char -> T.Text
hexCodePoint c = "U+" <> T.pack (pad4 (map toUpper (showHex (ord c) "")))
  where pad4 h = replicate (4 - length h) '0' ++ h
