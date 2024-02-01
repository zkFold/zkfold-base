{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC.Builtins where

import           Data.Typeable                         (Typeable, Proxy (..))
import           Prelude                               (Eq, ($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Cardano.UPLC.Type
import           ZkFold.Symbolic.Compiler

-- TODO: Add the actual builtins available on-chain in Plutus V3

-- | A class for built-in functions in Plutus.
class PlutusBuiltinFunction a fun where
    builtinFunctionType :: fun -> SomeType a
    builtinFunctionRep  :: fun -> SomeArithmetizable a

data BuiltinFunctions =
      AddField
    | MulField

-- TODO: use shortcuts to make these definitions more readable
instance forall a . (FiniteField a, Eq a, ToBits a, Typeable a) => PlutusBuiltinFunction a BuiltinFunctions where
    builtinFunctionType AddField =
          SomeFunction (SomeData $ Proxy @(ArithmeticCircuit a))
        $ SomeFunction (SomeData $ Proxy @(ArithmeticCircuit a))
        $ SomeData $ Proxy @(ArithmeticCircuit a)
    builtinFunctionType MulField =
        SomeFunction (SomeData $ Proxy @(ArithmeticCircuit a))
        $ SomeFunction (SomeData $ Proxy @(ArithmeticCircuit a))
        $ SomeData $ Proxy @(ArithmeticCircuit a)

    builtinFunctionRep AddField = SomeArithmetizable $ \(x :: ArithmeticCircuit a) (y :: ArithmeticCircuit a) -> x + y
    builtinFunctionRep MulField = SomeArithmetizable $ \(x :: ArithmeticCircuit a) (y :: ArithmeticCircuit a) -> x * y

