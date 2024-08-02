{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.UPLC.Builtins where

import           Data.Typeable                     (Proxy (..), Typeable)
import           GHC.Generics                      (Par1)
import           GHC.TypeLits                      (KnownNat)
import           Prelude                           (($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Cardano.UPLC.Type
import qualified ZkFold.Symbolic.Data.Class        as S

-- TODO: Add the actual builtins available on-chain in Plutus V3

-- | A class for built-in functions in Plutus.
class PlutusBuiltinFunction c fun where
    builtinFunctionType :: fun -> SomeType c
    builtinFunctionRep  :: fun -> S.SomeData c

data BuiltinFunctions =
      AddField
    | MulField

-- TODO: use shortcuts to make these definitions more readable
instance
    ( Typeable c
    , S.SymbolicData c (c Par1)
    , KnownNat (S.TypeSize c (c Par1))
    , Semiring (c Par1)
    ) => PlutusBuiltinFunction c BuiltinFunctions where

    builtinFunctionType AddField =
          SomeFunction (SomeSym $ SomeData $ Proxy @(c Par1))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(c Par1))
        $ SomeSym $ SomeData $ Proxy @(c Par1)
    builtinFunctionType MulField =
        SomeFunction (SomeSym $ SomeData $ Proxy @(c Par1))
        $ SomeFunction (SomeSym $ SomeData $ Proxy @(c Par1))
        $ SomeSym $ SomeData $ Proxy @(c Par1)

    builtinFunctionRep AddField = S.SomeData $ \(x :: c Par1) (y :: c Par1) -> x + y
    builtinFunctionRep MulField = S.SomeData $ \(x :: c Par1) (y :: c Par1) -> x * y
