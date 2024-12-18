{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.UTCTime where

import           GHC.Natural                      (Natural)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Class  (FromConstant)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators (RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt

newtype UTCTime c = UTCTime (UInt 11 Auto c)

deriving newtype instance Eq (UInt 11 Auto c) => Eq (UTCTime c)

deriving newtype instance Symbolic c => SymbolicData (UTCTime c)

deriving newtype instance Symbolic c => FromConstant Natural (UTCTime c)
