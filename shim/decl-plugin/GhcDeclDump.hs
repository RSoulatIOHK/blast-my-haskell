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
import qualified GHC.Core.Class             as Cls
import           GHC.Core.Predicate         (getClassPredTys_maybe, isPredTy)
import qualified GHC.Core.Type              as Type
import           GHC.Core.TyCo.Rep          (scaledThing)
import           GHC.Core.InstEnv           (ClsInst (..))
import           GHC.Types.FieldLabel       (FieldLabel (..))
import           GHC.Data.FastString        (unpackFS)
import           GHC.Types.Unique           (getKey)
import           Data.Maybe                 (isJust, mapMaybe)

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
      -- The *class* TyCons `isUserDataTyCon` filters out (see its `not
      -- (isClassTyCon tc)` clause) are exactly the ones we want here: the class
      -- SHAPE (params, superclasses, method signatures, which methods have
      -- defaults) exists nowhere in the Core dump — class-op Ids and `$p`
      -- superclass selectors are not top-level binds — so this is the only
      -- channel that can carry it.
      classDecls = map ppClass (mapMaybe tyConClass_maybe (tcg_tcs tcg))
  BSL.writeFile path . A.encode $
    A.object [ "module"     A..= modN
             , "typeDecls"  A..= typeDecls
             , "instances"  A..= instances
             , "classDecls" A..= classDecls
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

------------------------------------------------------------------------
-- Class declarations (shapes)
------------------------------------------------------------------------

-- | The GHC 9.2.7 API this section rests on (verified with
-- @ghci-9.2.7 -package ghc@, not from memory):
--
-- > tyConClass_maybe     :: TyCon -> Maybe Class            -- GHC.Core.TyCon
-- > Cls.classTyVars      :: Class -> [TyVar]                -- GHC.Core.Class
-- > Cls.classSCTheta     :: Class -> [PredType]             -- GHC.Core.Class
-- > Cls.classOpItems     :: Class -> [ClassOpItem]          -- GHC.Core.Class
-- > type ClassOpItem      = (Id, DefMethInfo)               -- GHC.Core.Class
-- > type DefMethInfo      = Maybe (Name, DefMethSpec Type)  -- GHC.Core.Class
-- > data DefMethSpec ty   = VanillaDM | GenericDM ty        -- GHC.Types.Basic
-- > getClassPredTys_maybe :: PredType -> Maybe (Class, [Type])  -- GHC.Core.Predicate
--
-- Note the plan's guess (@Maybe (Id, DefMethSpec)@) was off: the @Maybe@ sits on
-- the SECOND component of the pair, and it carries the default method's 'Name'
-- (@$dm<method>@), not an 'Id'. @isJust@ on it is the @hasDefault@ discriminator;
-- the 'Name' inside is what M3 Task 4 will want (a one-line addition here).
ppClass :: Cls.Class -> A.Value
ppClass cls = A.object
  [ "name"    A..= occNameString (nameOccName (Cls.className cls))
  , "tyVars"  A..= map (occNameString . nameOccName . tyVarName) (Cls.classTyVars cls)
  , "supers"  A..= map ppSuperPred (Cls.classSCTheta cls)
  , "methods" A..= map ppClassOp (Cls.classOpItems cls)
  ]

-- | A superclass constraint reduced to the parent class's NAME. Task 5 consumes
-- these as `extends <Name>` / builtin-binder recipes, for which the name is
-- exactly the payload; the argument types are recoverable from `classTyVars`
-- for the single-param case and are deliberately not dumped yet.
--
-- A superclass predicate that is not a class constraint at all (an equality
-- constraint, say) has no name to give. It is NOT dropped — a silently-dropped
-- superclass would be a silent-wrong downstream — but rendered as the reserved
-- name @_UnknownSuper@, which has no Lean image.
--
-- WHAT "no Lean image" BUYS, as of M3 Task 5 (which now consumes @supers@): the
-- name reaches neither @extends@ (it is not a locally-declared class) nor a
-- builtin binder recipe (@Maps.classConMap@ has no entry), so the emitted Lean
-- class omits the superclass and the transpiler prints
-- @Emit.unmappedSuperWarning@ for it. The loudness is that warning plus a
-- @failed to synthesize@ at any use site — NOT, as this comment previously
-- claimed, an emitted unknown identifier. Still unexercised: no fixture produces
-- a non-class superclass predicate.
ppSuperPred :: Type.PredType -> A.Value
ppSuperPred p = A.toJSON $ case getClassPredTys_maybe p of
  Just (c, _) -> occNameString (nameOccName (Cls.className c))
  Nothing     -> "_UnknownSuper"

ppClassOp :: Cls.ClassOpItem -> A.Value
ppClassOp (selId, dmInfo) = A.object
  [ "name"       A..= occNameString (nameOccName (varName selId))
  , "type"       A..= ppMethodTy (methodBodyTy (varType selId))
  , "hasDefault" A..= isJust dmInfo
  ]

-- | Strip a class-method SELECTOR type back to the signature as written in the
-- class body: @size :: forall a. Sized a => a -> Int@ ⇒ @a -> Int@. The class's
-- own quantifiers are dropped (the Lean `class` binds them) and so is the class
-- dictionary argument. Recursive, so a method with its own `forall`/constraints
-- (e.g. @m :: forall b. Eq b => a -> b -> Bool@) sheds those too — which loses
-- information the Lean side cannot use yet; recovering per-method constraints is
-- out of scope until a fixture needs it.
--
-- WHERE that loss shows is asymmetric, and the class side is the bad half.
-- Shedding @forall b.@ leaves @b@ free in the emitted @m : a -> b -> Bool@ and
-- Lean's @autoImplicit@ absorbs it in silence. OBSERVED at the settings that
-- actually apply to generated files (the emitter writes no @set_option@ and
-- @lakefile.toml@ sets no @leanOptions@, so the on-by-default value holds):
--
--     class Foo (a : Type) where
--       m : a → b → Bool
--     #check @Foo.m
--     ⇒ @Foo.m : {a : Type} → [self : Foo a] → {b : Sort u_1} → a → b → Bool
--
-- The class therefore ELABORATES CLEANLY while meaning something the Haskell did
-- not: @b@ became a per-method implicit, universe-polymorphic and entirely
-- unconstrained, where the source said @forall b. Eq b =>@. The shed CONSTRAINT
-- is the loud half — the instance's method body still needs the @Eq b@ the class
-- no longer asks for, and fails there. (That half is PREDICTED, not observed: no
-- fixture declares a method with its own quantifier, which is also why the
-- recovery is deferred.) Net: the silent-wrong sits exactly where nothing checks.
--
-- Candidate hardening for whoever picks this up, VERIFIED effective: under
-- @set_option autoImplicit false@ the very same class is rejected outright —
-- @error: Unknown identifier `b`@ — which converts the silent class-side half
-- into an elaboration error. Deliberately NOT done here: it would touch every
-- generated file, and this task only adds a dump channel.
methodBodyTy :: Type.Type -> Type.Type
methodBodyTy ty =
  let ty' = Type.dropForAlls ty
  in case Type.splitFunTy_maybe ty' of
       Just (_, arg, res) | isPredTy arg -> methodBodyTy res
       _                                 -> ty'

-- | Type serialisation for METHOD types. Deliberately separate from 'ppType'
-- (which serves data fields and instance heads) for two reasons, both of which
-- would otherwise corrupt method types:
--
--   * 'ppType' tries @splitTyConApp_maybe@ FIRST, and in GHC 9.2 that succeeds
--     on a @FunTy@ — decomposing @a -> Int@ into the 5-argument linear-types
--     @FUN@ application (multiplicity + two RuntimeReps + arg + res) instead of
--     an arrow. Method types are function types essentially always, so the
--     arrow case has to be tried first.
--   * 'ppType' has no type-VARIABLE case, so @a@ collapses to @_Unknown@ —
--     and a class method's type is precisely the one place type variables are
--     the point.
--
-- Keeping the two functions apart also keeps the existing @typeDecls@/
-- @instances@ output byte-identical by construction: this task adds a channel,
-- it does not re-render the old ones.
ppMethodTy :: Type.Type -> A.Value
ppMethodTy ty = case Type.getTyVar_maybe ty of
  Just tv -> A.object
    [ "tag"  A..= ("TyVar" :: T.Text)
    , "name" A..= occNameString (nameOccName (tyVarName tv))
    ]
  Nothing -> case Type.splitFunTy_maybe ty of
    Just (_, a, r) -> A.object
      [ "tag" A..= ("TyFun" :: T.Text)
      , "arg" A..= ppMethodTy a
      , "res" A..= ppMethodTy r
      ]
    Nothing -> case Type.splitTyConApp_maybe ty of
      Just (tc, args) -> A.object
        [ "tag"  A..= ("TyCon" :: T.Text)
        , "name" A..= occNameString (nameOccName (tyConName tc))
        , "args" A..= map ppMethodTy args
        ]
      Nothing -> A.object
        [ "tag"  A..= ("TyCon" :: T.Text)
        , "name" A..= ("_Unknown" :: T.Text)
        , "args" A..= ([] :: [A.Value])
        ]
