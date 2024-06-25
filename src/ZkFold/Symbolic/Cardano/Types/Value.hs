{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types.Value where

import           GHC.Generics                          (Generic1, Generically1 (..), (:.:))
import           Prelude                               (Foldable, Functor, Traversable)

import           ZkFold.Base.Algebra.Basic.Class       (DiscreteField, FiniteField)
import           ZkFold.Base.Algebra.Basic.VectorSpace (VectorSpace)
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Symbolic.Data.Bool             (Eq)
import           ZkFold.Symbolic.Data.ByteString       (ByteString)
import           ZkFold.Symbolic.Data.UInt             (UInt)

type Value n = Vector n :.: Policy

data Policy a = Policy
  { policyId    :: ByteString 224 a
  , assetName   :: ByteString 256 a
  , assetAmount :: UInt 64 a
  } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 Policy
  instance (FiniteField a) => VectorSpace a Policy
instance (FiniteField a, DiscreteField a) => Eq a Policy
