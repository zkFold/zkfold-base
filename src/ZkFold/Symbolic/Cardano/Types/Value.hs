{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Value where

import           GHC.Natural                         (Natural)
import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Compiler
import qualified ZkFold.Symbolic.Data.FieldElement   as FE

type PolicyId context    = ByteString 224 context
type AssetName context   = ByteString 256 context
type SingleAsset context = (PolicyId context, (AssetName context, UInt 64 context))

newtype Value n context = Value { getValue :: Vector n (SingleAsset context) }

deriving instance FE.FieldElementData F CtxEvaluation (Value n CtxEvaluation)

deriving instance SymbolicData F (Value n CtxCompilation)

-- TODO
instance Semigroup (Value n context) where
    (<>) = undefined

-- TODO
instance Monoid (Value n context) where
    mempty = undefined

instance AdditiveSemigroup (Value n context) where
    (+) = (<>)

instance Scale Natural (Value n context) => AdditiveMonoid (Value n context) where
    zero = mempty
