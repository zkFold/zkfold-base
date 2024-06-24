{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
module ZkFold.Symbolic.Cardano.IsData.TH where

import           Data.Functor                         ((<&>))
import           Data.Maybe                           (Maybe (..))
import           Data.Traversable                     (for)
import qualified Language.Haskell.TH                  as TH
import qualified Language.Haskell.TH.Datatype         as TH
import           Prelude                              (Applicative (..), Foldable (..), Functor (..), Int, Integer,
                                                       MonadFail (..), Show (..), fromIntegral, lookup, zip, ($), (++),
                                                       (<$>), (=<<))

import qualified ZkFold.Symbolic.Cardano.Builtins     as BI
import           ZkFold.Symbolic.Cardano.IsData.Class (ToData (..))


mkConstrCreateExpr :: Integer -> [TH.Name] -> TH.ExpQ
mkConstrCreateExpr conIx createFieldNames =
  let
    createArgsExpr :: TH.ExpQ
    createArgsExpr = foldr
      (\v e -> [| BI.mkCons (toBuiltinData $(TH.varE v)) $e |])
      [| BI.mkNilData BI.unitval |]
      createFieldNames
    createExpr = [| BI.mkConstr (conIx :: Integer) $createArgsExpr |]
  in createExpr

toDataClause :: (TH.ConstructorInfo, Int) -> TH.Q TH.Clause
toDataClause (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    let create = mkConstrCreateExpr (fromIntegral index) argNames
    TH.clause [TH.conP name (fmap TH.varP argNames)] (TH.normalB create) []

toDataClauses :: [(TH.ConstructorInfo, Int)] -> [TH.Q TH.Clause]
toDataClauses indexedCons = toDataClause <$> indexedCons

defaultIndex :: TH.Name -> TH.Q [(TH.Name, Int)]
defaultIndex name = do
    info <- TH.reifyDatatype name
    pure $ zip (TH.constructorName <$> TH.datatypeCons info) [0..]

-- | Generate a 'FromData' and a 'ToData' instance for a type.
-- This may not be stable in the face of constructor additions,
-- renamings, etc. Use 'makeIsDataIndexed' if you need stability.
unstableMakeIsData :: TH.Name -> TH.Q [TH.Dec]
unstableMakeIsData name = makeIsDataIndexed name =<< defaultIndex name

-- | Generate a 'ToData', 'FromData and a 'UnsafeFromData' instances for a type,
-- using an explicit mapping of constructor names to indices.
-- Use this for types where you need to keep the representation stable.
makeIsDataIndexed :: TH.Name -> [(TH.Name, Int)] -> TH.Q [TH.Dec]
makeIsDataIndexed dataTypeName indices = do
  dataTypeInfo <- TH.reifyDatatype dataTypeName
  let appliedType = TH.datatypeType dataTypeInfo
  let nonOverlapInstance = TH.InstanceD Nothing

  indexedCons <- for (TH.datatypeCons dataTypeInfo) $ \ctorInfo ->
    case lookup (TH.constructorName ctorInfo) indices of
      Just i  -> pure (ctorInfo, i)
      Nothing -> fail $ "No index given for constructor" ++ show (TH.constructorName ctorInfo)

  toDataInst <- do
    let constraints = TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
          TH.classPred ''ToData [TH.VarT (tyvarbndrName tyVarBinder)]
    toDataDecl <- TH.funD 'toBuiltinData (toDataClauses indexedCons)
    toDataPrag <- TH.pragInlD 'toBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $ nonOverlapInstance
      constraints
      (TH.classPred ''ToData [appliedType])
      [toDataPrag, toDataDecl]

  pure [toDataInst]

tyvarbndrName :: TH.TyVarBndr flag -> TH.Name
tyvarbndrName (TH.PlainTV n _)    = n
tyvarbndrName (TH.KindedTV n _ _) = n
