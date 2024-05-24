{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.UTCTime where
    
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.UInt

import qualified Prelude

newtype UTCTime a = UTCTime (UInt 11 a)
  deriving stock
    ( Prelude.Eq
    , Prelude.Show
    , Prelude.Functor
    , Prelude.Foldable
    , Prelude.Traversable
    )

deriving newtype instance FiniteField a => VectorSpace a UTCTime
instance Eq a UTCTime
