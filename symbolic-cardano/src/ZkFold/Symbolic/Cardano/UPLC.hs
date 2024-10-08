{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Cardano.UPLC where

import           Data.Maybe                             (fromJust)
import           Data.Type.Equality                     (type (~))
import           Data.Typeable                          (Proxy (..), Typeable, cast)
import           Prelude                                (Eq (..), error, otherwise, snd, ($))

import           ZkFold.Symbolic.Cardano.UPLC.Builtins
import           ZkFold.Symbolic.Cardano.UPLC.Inference
import           ZkFold.Symbolic.Cardano.UPLC.Term
import           ZkFold.Symbolic.Cardano.UPLC.Type
import qualified ZkFold.Symbolic.Data.Class             as S
import           ZkFold.Symbolic.Data.Class             (SymbolicData)

-- TODO: we need to figure out what to do with error terms

data ArgList name c where
    ArgListEmpty :: ArgList name c
    ArgListCons  :: (Typeable t, SymbolicData t, S.Context t ~ c) => (name, t) -> ArgList name c -> ArgList name c

class FromUPLC name fun c where
    fromUPLC :: ArgList name c -> Term name fun c -> S.SomeData c

instance forall name fun c . (Eq name, Typeable name, Typeable fun, Eq fun, PlutusBuiltinFunction c fun, Typeable c) => FromUPLC name fun c where
    fromUPLC ArgListEmpty (Var _) = error "fromUPLC: unknown variable"
    fromUPLC (ArgListCons (x, t) xs) (Var y)
        | x == y    = S.SomeData t
        | otherwise = fromUPLC @name @fun xs (Var y)
    fromUPLC args term@(LamAbs x f) =
        case snd $ inferTypes @name @fun term of
            SomeFunction t1 t2 ->
                let t1' = functionToData t1
                    t2' = functionToData t2
                in case (t1', t2') of
                    (SomeSym (SomeData (_ :: Proxy t1)), SomeSym (SomeData (_ :: Proxy t2))) ->
                        S.SomeData @(t1 -> t2) $ \arg ->
                            case fromUPLC (ArgListCons (x, arg) args) f of
                                S.SomeData res -> fromJust $ cast res
                    _ -> error "fromUPLC: LamAbs"
            _ -> error "fromUPLC: LamAbs"
    fromUPLC args (Apply f x) =
        case snd $ inferTypes @name @fun f of
            SomeFunction t1 t2 ->
                let t1' = functionToData t1
                    t2' = functionToData t2
                in case (t1', t2', fromUPLC args f, fromUPLC args x) of
                    (SomeSym (SomeData (_ :: Proxy t1)), SomeSym (SomeData (_ :: Proxy t2)), S.SomeData f', S.SomeData x') ->
                        S.SomeData ((fromJust $ cast @_ @(t1 -> t2) f') (fromJust $ cast @_ @t1 x') :: t2)
                    _ -> error "fromUPLC: Apply"
            _ -> error "fromUPLC: Apply"
    fromUPLC args (Force t) = fromUPLC args t
    fromUPLC args (Delay t) = fromUPLC args t
    fromUPLC _ (Constant c) = S.SomeData c
    fromUPLC _ (Builtin b)  = builtinFunctionRep b
    fromUPLC _ Error        = error "fromUPLC: Error"

-- TODO: No idea how to define type-level input size here
{--
instance forall name (a :: Type) . (Typeable name, Eq name, Eq BuiltinFunctions, Typeable a, Arithmetic a)
        => Arithmetizable a (Term name BuiltinFunctions a) where

    arithmetize term = case fromUPLC @name @_ @a ArgListEmpty term of
        SomeArithmetizable t -> arithmetize t
--}
