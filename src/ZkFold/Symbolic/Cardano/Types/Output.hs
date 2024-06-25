{-# LANGUAGE DerivingVia, UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types.Output where

import           GHC.Generics                          (Generic1, Generically1 (..))
import           GHC.TypeNats                          (KnownNat)
import           Prelude                               (Functor, Foldable, Traversable)

import           ZkFold.Base.Algebra.Basic.Class       (DiscreteField, FiniteField)
import           ZkFold.Base.Algebra.Basic.VectorSpace (VectorSpace)
import           ZkFold.Symbolic.Cardano.Types.Address (Address)
import           ZkFold.Symbolic.Cardano.Types.Value   (Value)
import           ZkFold.Symbolic.Data.Bool             (Eq)
import           ZkFold.Symbolic.Data.ByteString       (ByteString)

type DatumHash = ByteString 256

data Output tokens datum a = Output 
  { txoAddress :: Address a
  , txoTokens :: Value tokens a
  , txoDatumHash :: DatumHash a
  } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 (Output tokens datum)
  instance (FiniteField a, KnownNat tokens) => VectorSpace a (Output tokens datum)
instance (FiniteField a, DiscreteField a, KnownNat tokens) => Eq a (Output tokens datum)
