{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types.Input where

import           GHC.Generics                            (Generic1, Generically1 (..))
import           GHC.TypeNats                            (KnownNat)
import           Prelude                                 (Foldable, Functor, Traversable, (.))

import           ZkFold.Base.Algebra.Basic.Class         (DiscreteField, FiniteField)
import           ZkFold.Base.Algebra.Basic.VectorSpace   (VectorSpace)
import           ZkFold.Symbolic.Cardano.Types.Address   (Address)
import           ZkFold.Symbolic.Cardano.Types.Output    (DatumHash, Output, txoAddress, txoDatumHash, txoTokens)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value     (Value)
import           ZkFold.Symbolic.Data.Bool               (Eq)

data Input tokens datum a = Input
  { txiOutputRef :: OutputRef a
  , txiOutput    :: Output tokens datum a
  } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 (Input tokens datum)
  instance (FiniteField a, KnownNat tokens) => VectorSpace a (Input tokens datum)
instance (FiniteField a, DiscreteField a, KnownNat tokens) => Eq a (Input tokens datum)

txiAddress :: Input tokens datum a -> Address a
txiAddress = txoAddress . txiOutput

txiTokens :: Input tokens datum a -> Value tokens a
txiTokens = txoTokens . txiOutput

txiDatumHash :: Input tokens datum a -> DatumHash a
txiDatumHash = txoDatumHash . txiOutput
