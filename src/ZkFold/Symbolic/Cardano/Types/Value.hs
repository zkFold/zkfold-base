{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Value where

import           GHC.Natural                         (Natural)
import           Prelude                             hiding (Bool, Eq, length, splitAt, replicate, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number    (KnownNat, value)
import           ZkFold.Base.Data.Vector
import           ZkFold.Prelude                      (replicate)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString     (Concat)
import qualified ZkFold.Symbolic.Data.FieldElement   as FE

type PolicyId context    = ByteString 224 context
type AssetName context   = ByteString 256 context
type SingleAsset context = (PolicyId context, (AssetName context, UInt 64 context))

newtype Value n context = Value { getValue :: Vector n (SingleAsset context) }

deriving instance (Haskell.Eq (ByteString 224 context), Haskell.Eq (ByteString 256 context), Haskell.Eq (UInt 64 context))
    => Haskell.Eq (Value n context)

deriving instance FE.FieldElementData F CtxEvaluation (Value n CtxEvaluation)

deriving instance SymbolicData F (Value n CtxCompilation)

instance (FromConstant Natural (UInt 64 context), MultiplicativeSemigroup (UInt 64 context))
        => Scale Natural (Value n context) where
    n `scale` Value v = Value $ fmap (\(pid, (aname, q)) -> (pid, (aname, n `scale` q))) v

-- TODO
instance Semigroup (Value n context) where
    (<>) = undefined

-- TODO
instance
    ( KnownNat n
    , FromConstant Natural (UInt 64 context)
    , Concat (ByteString 8 context) (ByteString 224 context)
    , Concat (ByteString 8 context) (ByteString 256 context)
    , FromConstant Natural (ByteString 8 context)
    ) => Monoid (Value n context) where
    mempty = Value $ Vector $ replicate (value @n) ("", ("", fromConstant @Natural 0))

instance AdditiveSemigroup (Value n context) where
    (+) = (<>)

instance 
    ( KnownNat n
    , FromConstant Natural (UInt 64 context)
    , Concat (ByteString 8 context) (ByteString 224 context)
    , Concat (ByteString 8 context) (ByteString 256 context)
    , FromConstant Natural (ByteString 8 context)
    , Scale Natural (Value n context)
     ) => AdditiveMonoid (Value n context) where
    zero = mempty
