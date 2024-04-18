{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC.Inference where

import           Data.Maybe                                      (fromMaybe, maybeToList)
import           Data.Typeable                                   (Proxy (..))
import           Prelude

import           ZkFold.Symbolic.Cardano.UPLC.Builtins
import           ZkFold.Symbolic.Cardano.UPLC.Inference.Internal
import           ZkFold.Symbolic.Cardano.UPLC.Term
import           ZkFold.Symbolic.Cardano.UPLC.Type

-- TODO: Variable names must be unique for this to work!
-- TODO: Properly infer polymorphic type instantiations

inferType :: forall name fun a . (Eq name, Eq fun, PlutusBuiltinFunction a fun) =>
    (Term name fun a, SomeType a) -> TypeList name fun a -> TypeList name fun a
inferType (Var x, t) types =
    let mf = (, SomeFunction t NoType) <$> findLambda x types
    in updateTypeList types $ maybeToList mf
inferType (LamAbs x f, SomeFunction t1 t2) types =
    updateTypeList types [(Var x, t1), (f, t2)]
inferType (Apply f x, t2) types =
    let t1  = fromMaybe NoType $ findTermType x types
        t   = case fromMaybe NoType $ findTermType f types of
            SomeFunction _ t2' -> t2'
            _                  -> NoType
    in updateTypeList types [(f, SomeFunction t1 t2), (Apply f x, t)]
inferType (Force x, t) types =
    updateTypeList types [(x, t)]
inferType (Delay x, t) types =
    updateTypeList types [(x, t)]
inferType (Constant (c :: c), _) types =
    updateTypeList types [(Constant c, SomeSym $ SomeData (Proxy :: Proxy c))]
inferType (Builtin b, _) types =
    updateTypeList types [(Builtin b, builtinFunctionType b)]
inferType (Error, _) types =
    updateTypeList types [(Error, AnyType)]
inferType _ types = types

inferTypes :: forall name fun a . (Eq name, Eq fun, PlutusBuiltinFunction a fun) =>
    Term name fun a -> (Term name fun a, SomeType a)
inferTypes term = head $ go (makeTypeList term)
    where
        go types =
            let types' = foldr inferType types types
            in if types == types' then types else types'

-- To obtain an arithmetizable term, we need all types to be concrete.
inferSuccess :: forall name fun a . (Eq name, Eq fun) => SomeType a -> Bool
inferSuccess (SomeSym _)          = True
inferSuccess (SomeFunction t1 t2) = inferSuccess @name @fun t1 && inferSuccess @name @fun t2
inferSuccess _                    = False
