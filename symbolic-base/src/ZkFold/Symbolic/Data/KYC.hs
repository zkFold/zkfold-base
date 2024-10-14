{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Data.KYC where

import           Data.Aeson
import           GHC.Generics                     (Generic)

import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Data.Vector          (Vector)
import           ZkFold.Symbolic.Class            (Symbolic)
import           ZkFold.Symbolic.Data.Bool        (Bool)
import           ZkFold.Symbolic.Data.ByteString  (ByteString)
import           ZkFold.Symbolic.Data.Combinators (RegisterSize (..))
import           ZkFold.Symbolic.Data.Eq          (elem)
import           ZkFold.Symbolic.Data.UInt        (UInt)
import           ZkFold.Symbolic.Interpreter      (Interpreter)


type KYCByteString context = ByteString 256 context

data KYCData context = KYCData
    { kycType  :: KYCByteString context
    , kycValue :: KYCByteString context
    , kycHash  :: KYCByteString context
    , kycID    :: UInt 64 Auto context
    } deriving Generic

instance (Symbolic context) => FromJSON (KYCData context)
instance (Symbolic (Interpreter (Zp p))) => ToJSON (KYCData (Interpreter (Zp p)))


isCitizen :: (Symbolic c) => KYCByteString c -> Vector n (KYCByteString c) -> Bool c
isCitizen = elem
