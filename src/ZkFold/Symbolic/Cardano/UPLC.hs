{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Cardano.UPLC where

import           Data.Kind                              (Type)
import           Data.Maybe                             (fromJust)
import           Data.Typeable                          (Proxy (..), Typeable, cast)
import           Prelude                                (Eq (..), error, otherwise, snd, ($))

import           ZkFold.Symbolic.Cardano.UPLC.Builtins
import           ZkFold.Symbolic.Cardano.UPLC.Inference
import           ZkFold.Symbolic.Cardano.UPLC.Term
import           ZkFold.Symbolic.Cardano.UPLC.Type
import qualified ZkFold.Symbolic.Compiler               as AC

-- TODO: we need to figure out what to do with error terms

data ArgList name a where
    ArgListEmpty :: ArgList name a
    ArgListCons  :: (Typeable t, AC.SymbolicData a t) => (name, t) -> ArgList name a -> ArgList name a

class FromUPLC name fun a where
    fromUPLC :: ArgList name a -> Term name fun a -> AC.SomeData a

instance forall name fun (a :: Type) . (Eq name, Typeable name, Typeable fun, Eq fun, PlutusBuiltinFunction a fun, Typeable a) => FromUPLC name fun a where
    fromUPLC ArgListEmpty (Var _) = error "fromUPLC: unknown variable"
    fromUPLC (ArgListCons (x, t) xs) (Var y)
        | x == y    = AC.SomeData t
        | otherwise = fromUPLC @name @fun xs (Var y)
    fromUPLC args term@(LamAbs x f) =
        case snd $ inferTypes @name @fun term of
            SomeFunction t1 t2 ->
                let t1' = functionToData t1
                    t2' = functionToData t2
                in case (t1', t2') of
                    (SomeSym (SomeData (_ :: Proxy t1)), SomeSym (SomeData (_ :: Proxy t2))) ->
                        AC.SomeData $ \(arg :: t1) ->
                            case fromUPLC (ArgListCons (x, arg) args) f of
                                AC.SomeData res -> fromJust $ cast @_ @t2 res
                    _ -> error "fromUPLC: LamAbs"
            _ -> error "fromUPLC: LamAbs"
    fromUPLC args (Apply f x) =
        case snd $ inferTypes @name @fun f of
            SomeFunction t1 t2 ->
                let t1' = functionToData t1
                    t2' = functionToData t2
                in case (t1', t2', fromUPLC args f, fromUPLC args x) of
                    (SomeSym (SomeData (_ :: Proxy t1)), SomeSym (SomeData (_ :: Proxy t2)), AC.SomeData f', AC.SomeData x') ->
                        AC.SomeData ((fromJust $ cast @_ @(t1 -> t2) f') (fromJust $ cast @_ @t1 x') :: t2)
                    _ -> error "fromUPLC: Apply"
            _ -> error "fromUPLC: Apply"
    fromUPLC args (Force t) = fromUPLC args t
    fromUPLC args (Delay t) = fromUPLC args t
    fromUPLC _ (Constant c) = AC.SomeData c
    fromUPLC _ (Builtin b)  = builtinFunctionRep b
    fromUPLC _ Error        = error "fromUPLC: Error"

-- TODO: No idea how to define type-level input size here
{--
instance forall name (a :: Type) . (Typeable name, Eq name, Eq BuiltinFunctions, Typeable a, Arithmetic a)
        => Arithmetizable a (Term name BuiltinFunctions a) where

    arithmetize term = case fromUPLC @name @_ @a ArgListEmpty term of
        SomeArithmetizable t -> arithmetize t
--}
