{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Value where

import           GHC.Natural                         (Natural)
import           Prelude                             hiding (Bool, Eq, length, replicate, splitAt, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Compiler
import qualified ZkFold.Symbolic.Data.FieldElement   as FE
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize(..))

type PolicyId context    = ByteString 224 context
type AssetName context   = ByteString 256 context
type SingleAsset context = (PolicyId context, (AssetName context, UInt 64 context Auto))

newtype Value n context = Value { getValue :: Vector n (SingleAsset context) }

deriving instance (Haskell.Eq (ByteString 224 context), Haskell.Eq (ByteString 256 context), Haskell.Eq (UInt 64 context Auto))
    => Haskell.Eq (Value n context)

deriving instance FE.FieldElementData CtxEvaluation (Value n CtxEvaluation)

deriving instance SymbolicData F (Value n CtxCompilation)

instance (FromConstant Natural (UInt 64 context Auto), MultiplicativeSemigroup (UInt 64 context Auto))
        => Scale Natural (Value n context) where
    n `scale` Value v = Value $ fmap (\(pid, (aname, q)) -> (pid, (aname, n `scale` q))) v

-- TODO
instance Semigroup (Value n context) where
    (<>) _ _ = undefined

-- TODO
instance Monoid (Value n context) where
    mempty = undefined

instance AdditiveSemigroup (Value n context) where
    (+) = (<>)

instance
    ( FromConstant Natural (UInt 64 context Auto)
    , MultiplicativeSemigroup (UInt 64 context Auto)
    ) => AdditiveMonoid (Value n context) where
    zero = mempty
