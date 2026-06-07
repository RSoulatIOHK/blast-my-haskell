{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module GhcDeclDump (plugin) where

-- | A small GHC source plugin that captures the *shape* of data declarations
-- and class-instance heads from a module's TcGblEnv, writing them as JSON to
-- @<module>.decls.json@ alongside the build artefacts.
--
-- The instance method *bodies* are not emitted here — they're already in the
-- ghc-dump-core CBOR dump as ordinary top-level Var bindings. The JSON written
-- by this plugin gives the Lean side enough information to emit
-- `structure Foo where …` and `instance : BEq Foo where beq := <dfun-name>`,
-- referencing those existing definitions.

import qualified Data.Aeson                 as A
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.Text                  as T
import           System.Environment         (lookupEnv)
import           System.FilePath            ((</>))

import           GHC.Plugins
import           GHC.Tc.Types               (TcGblEnv (..))
import           GHC.Core.TyCon
import           GHC.Core.DataCon
import qualified GHC.Core.Type              as Type
import           GHC.Core.TyCo.Rep          (scaledThing)
import           GHC.Core.InstEnv           (ClsInst (..))
import           GHC.Types.FieldLabel       (FieldLabel (..))
import           GHC.Data.FastString        (unpackFS)
import           GHC.Types.Unique           (getKey)

------------------------------------------------------------------------
-- Plugin entry
------------------------------------------------------------------------

plugin :: Plugin
plugin = defaultPlugin
  { pluginRecompile       = purePlugin
  , typeCheckResultAction = \_ ms tcg -> do
      liftIO (dump ms tcg)
      pure tcg
  }

dump :: ModSummary -> TcGblEnv -> IO ()
dump ms tcg = do
  dir <- maybe "." id <$> lookupEnv "GHC_DECL_DUMP_DIR"
  let modN     = moduleNameString (moduleName (ms_mod ms))
      path     = dir </> (modN ++ ".decls.json")
      typeDecls = map ppTyCon
                . filter isUserDataTyCon
                $ tcg_tcs tcg
      instances = map ppClsInst (tcg_insts tcg)
  BSL.writeFile path . A.encode $
    A.object [ "module"     A..= modN
             , "typeDecls"  A..= typeDecls
             , "instances"  A..= instances
             ]

------------------------------------------------------------------------
-- Type declarations
------------------------------------------------------------------------

-- | Keep H98 data declarations introduced by the user; skip class TyCons,
-- newtype wrappers, type synonyms, and anything internal.
isUserDataTyCon :: TyCon -> Bool
isUserDataTyCon tc =
     isAlgTyCon tc
  && not (isClassTyCon tc)
  && not (isPromotedDataCon tc)
  && (isDataTyCon tc || isNewTyCon tc)

ppTyCon :: TyCon -> A.Value
ppTyCon tc = A.object
  [ "name"         A..= occNameString (nameOccName (tyConName tc))
  , "kind"         A..= (if isNewTyCon tc then ("newtype" :: T.Text) else "data")
  , "constructors" A..= map ppDataCon (tyConDataCons tc)
  ]

ppDataCon :: DataCon -> A.Value
ppDataCon dc =
  let fieldLabels = dataConFieldLabels dc
      argTys      = map scaledThing (dataConOrigArgTys dc)
      pairs       = zipFields fieldLabels argTys
  in A.object
       [ "name"   A..= occNameString (nameOccName (dataConName dc))
       , "fields" A..= map (uncurry ppField) pairs
       ]

zipFields :: [FieldLabel] -> [Type.Type] -> [(Maybe String, Type.Type)]
zipFields []  tys = map (\t -> (Nothing, t)) tys
zipFields fls tys = zip (map (Just . unpackFS . flLabel) fls) tys

ppField :: Maybe String -> Type.Type -> A.Value
ppField mLabel ty = A.object
  [ "name" A..= maybe ("_" :: String) id mLabel
  , "type" A..= ppType ty
  ]

-- | Type serialisation: enough for monomorphic data fields. Anything fancy
-- collapses to TyCon "_Unknown" — the Lean side already has a fallback for
-- this via `GHCCore.tyConOpaque`.
ppType :: Type.Type -> A.Value
ppType ty = case Type.splitTyConApp_maybe ty of
  Just (tc, args) -> A.object
    [ "tag"  A..= ("TyCon" :: T.Text)
    , "name" A..= occNameString (nameOccName (tyConName tc))
    , "args" A..= map ppType args
    ]
  Nothing -> case Type.splitFunTy_maybe ty of
    Just (_, a, r) -> A.object
      [ "tag" A..= ("TyFun" :: T.Text)
      , "arg" A..= ppType a
      , "res" A..= ppType r
      ]
    Nothing -> A.object
      [ "tag"  A..= ("TyCon" :: T.Text)
      , "name" A..= ("_Unknown" :: T.Text)
      , "args" A..= ([] :: [A.Value])
      ]

------------------------------------------------------------------------
-- Class instances
------------------------------------------------------------------------

ppClsInst :: ClsInst -> A.Value
ppClsInst ci = A.object
  [ "className"   A..= occNameString (nameOccName (is_cls_nm ci))
  , "headTypes"   A..= map ppType (is_tys ci)
  , "dfunName"    A..= occNameString (nameOccName (varName (is_dfun ci)))
  , "dfunUnique"  A..= getKey (nameUnique (varName (is_dfun ci)))
  ]
