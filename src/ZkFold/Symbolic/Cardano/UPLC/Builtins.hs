{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC.Builtins where

import           Data.Typeable                     (Proxy (..), Typeable)
import           GHC.Generics                      (Par1)
import           Prelude                           (($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Cardano.UPLC.Type
import qualified ZkFold.Symbolic.Compiler          as AC

-- TODO: Add the actual builtins available on-chain in Plutus V3

-- | A class for built-in functions in Plutus.
class PlutusBuiltinFunction a fun where
    builtinFunctionType :: fun -> SomeType a
    builtinFunctionRep  :: fun -> AC.SomeData a

data BuiltinFunctions =
      AddField
    | MulField

-- TODO: use shortcuts to make these definitions more readable
instance forall a . (AC.Arithmetic a, Typeable a) => PlutusBuiltinFunction a BuiltinFunctions where
    builtinFunctionType AddField =
          SomeFunction (SomeSym $ SomeData $ Proxy @(AC.ArithmeticCircuit a Par1))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(AC.ArithmeticCircuit a Par1))
        $ SomeSym $ SomeData $ Proxy @(AC.ArithmeticCircuit a Par1)
    builtinFunctionType MulField =
        SomeFunction (SomeSym $ SomeData $ Proxy @(AC.ArithmeticCircuit a Par1))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(AC.ArithmeticCircuit a Par1))
        $ SomeSym $ SomeData $ Proxy @(AC.ArithmeticCircuit a Par1)

    builtinFunctionRep AddField = AC.SomeData $ \(x :: AC.ArithmeticCircuit a Par1) (y :: AC.ArithmeticCircuit a Par1) -> x + y
    builtinFunctionRep MulField = AC.SomeData $ \(x :: AC.ArithmeticCircuit a Par1) (y :: AC.ArithmeticCircuit a Par1) -> x * y
