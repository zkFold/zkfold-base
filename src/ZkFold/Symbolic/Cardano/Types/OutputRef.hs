{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           GHC.Generics                          (Generic1, Generically1 (..))
import           Prelude                               (Foldable, Functor, Traversable)

import           ZkFold.Base.Algebra.Basic.Class       (DiscreteField, FiniteField)
import           ZkFold.Base.Algebra.Basic.VectorSpace (VectorSpace)
import           ZkFold.Symbolic.Data.Bool             (Eq)
import           ZkFold.Symbolic.Data.ByteString       (ByteString)
import           ZkFold.Symbolic.Data.UInt             (UInt)

data OutputRef a = OutputRef
  { outputRefId    :: ByteString 256 a
  , outputRefIndex :: UInt 32 a
  } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 OutputRef
  instance (FiniteField a) => VectorSpace a OutputRef
instance (FiniteField a, DiscreteField a) => Eq a OutputRef
