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

type PolicyId = ByteString 224
type AssetName = ByteString 256

data ValueElement a = ValueElement
  { policyId    :: PolicyId a
  , assetName   :: AssetName a
  , assetAmount :: UInt 64 a
  } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 ValueElement
  instance (FiniteField a) => VectorSpace a ValueElement
instance (FiniteField a, DiscreteField a) => Eq a ValueElement

type Value n = Vector n :.: ValueElement

-- newtype Value n a = Value { getValue :: Vector n (PolicyId a, (AssetName a, UInt 64 a)) }

-- deriving instance (Arithmetic a, KnownNat n) => SymbolicData a (Value n (ArithmeticCircuit a))
