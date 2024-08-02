{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- This is what our life will look like from now on if we keep using NumberOfRegisters

module ZkFold.Symbolic.Data.UTCTime where

import           GHC.Natural                      (Natural)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Class  (FromConstant)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators (RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt

newtype UTCTime c = UTCTime (UInt 11 Auto c)

deriving newtype instance Eq (UInt 11 Auto c) => Eq (UTCTime c)

deriving newtype instance SymbolicData c (UTCTime c)

deriving newtype instance FromConstant Natural (UInt 11 Auto c) => FromConstant Natural (UTCTime c)
