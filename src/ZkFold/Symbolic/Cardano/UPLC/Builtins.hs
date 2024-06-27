{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

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
          SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit 1 a))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit 1 a))
        $ SomeSym $ SomeData $ Proxy @(ArithmeticCircuit 1 a)
    builtinFunctionType MulField =
        SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit 1 a))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(ArithmeticCircuit 1 a))
        $ SomeSym $ SomeData $ Proxy @(ArithmeticCircuit 1 a)

    builtinFunctionRep AddField = SomeArithmetizable $ \(x :: ArithmeticCircuit 1 a) (y :: ArithmeticCircuit 1 a) -> x + y
    builtinFunctionRep MulField = SomeArithmetizable $ \(x :: ArithmeticCircuit 1 a) (y :: ArithmeticCircuit 1 a) -> x * y
