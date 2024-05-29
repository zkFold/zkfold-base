{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.UTCTime where

import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.UInt

newtype UTCTime a = UTCTime (UInt 11 a)
  deriving stock
    ( Prelude.Eq
    , Prelude.Show
    , Prelude.Functor
    , Prelude.Foldable
    , Prelude.Traversable
    )

deriving newtype instance FiniteField a => VectorSpace a UTCTime
instance (FiniteField a, DiscreteField a) => Eq a UTCTime
