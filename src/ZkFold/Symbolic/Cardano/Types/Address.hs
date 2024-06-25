{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types.Address where

import           GHC.Generics                          (Generic1, Generically1 (..))
import           Prelude                               (Foldable, Functor, Traversable)

import           ZkFold.Base.Algebra.Basic.Class       (DiscreteField, FiniteField)
import           ZkFold.Base.Algebra.Basic.VectorSpace (VectorSpace)
import           ZkFold.Symbolic.Data.Bool             (Eq)
import           ZkFold.Symbolic.Data.ByteString       (ByteString)

type AddressType = ByteString 4
type PaymentCredential = ByteString 224
type StakingCredential = ByteString 224

data Address a = Address
  { addressType       :: AddressType a
  , paymentCredential :: PaymentCredential a
  , stakingCredential :: StakingCredential a
  } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 Address
  instance (FiniteField a) => VectorSpace a Address
instance (FiniteField a, DiscreteField a) => Eq a Address
