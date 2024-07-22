{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC.Builtins where

import           Data.Typeable                     (Proxy (..), Typeable)
import           Prelude                           (($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Cardano.UPLC.Type
import           ZkFold.Symbolic.Compiler          (Arithmetic, ArithmeticCircuit, SomeArithmetizable (..))

-- TODO: Add the actual builtins available on-chain in Plutus V3

-- | A class for built-in functions in Plutus.
class PlutusBuiltinFunction a fun where
    builtinFunctionType :: fun -> SomeType a
    builtinFunctionRep  :: fun -> SomeArithmetizable a

data BuiltinFunctions =
      AddField
    | MulField

-- TODO: use shortcuts to make these definitions more readable
instance forall a . (Arithmetic a, Typeable a) => PlutusBuiltinFunction a BuiltinFunctions where
    builtinFunctionType AddField =
          SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit a 1))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit a 1))
        $ SomeSym $ SomeData $ Proxy @(ArithmeticCircuit a 1)
    builtinFunctionType MulField =
        SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit a 1))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit a 1))
        $ SomeSym $ SomeData $ Proxy @(ArithmeticCircuit a 1)

    builtinFunctionRep AddField = SomeArithmetizable $ \(x :: ArithmeticCircuit a 1) (y :: ArithmeticCircuit a 1) -> x + y
    builtinFunctionRep MulField = SomeArithmetizable $ \(x :: ArithmeticCircuit a 1) (y :: ArithmeticCircuit a 1) -> x * y
