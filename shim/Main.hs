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

-- | Splice `typeDecls` and `instances` from the decl-plugin's JSON into the
-- core-side JSON. If decls is Null (no plugin output), pass core through.
mergeDecls :: A.Value -> A.Value -> A.Value
mergeDecls core decls =
  case (core, decls) of
    (A.Object cobj, A.Object dobj) ->
      let pick k = maybe A.Null id (AKM.lookup k dobj)
          coreWith = AKM.insert "typeDecls" (pick "typeDecls")
                   $ AKM.insert "instances" (pick "instances")
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
      in if take 2 n `elem` ["$d", "$f"] then "dict" else "id"

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
      ECoercion -> object [ "tag" .= ("Cast" :: T.Text), "expr" .= object [] ]

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
      role = if T.take 2 nm `elem` ["$d", "$f"] then "dict" else "id"
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
  MachChar c    -> object [ "tag" .= ("LitChar"   :: T.Text), "value" .= T.singleton c ]
  MachStr _     -> object [ "tag" .= ("LitString" :: T.Text), "value" .= ("<bs>" :: T.Text) ]
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
