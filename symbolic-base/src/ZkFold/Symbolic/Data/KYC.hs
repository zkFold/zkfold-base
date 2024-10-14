{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Data.KYC where

import           GHC.Generics                        (Generic)

import           ZkFold.Base.Data.Vector             (Vector)
import           ZkFold.Symbolic.Data.ByteString (ByteString)
import           ZkFold.Symbolic.Class               (Symbolic)
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize (..))
import           ZkFold.Symbolic.Data.Eq             (elem)
import ZkFold.Symbolic.Data.UInt (UInt)
import ZkFold.Symbolic.Data.Bool (Bool)
import Data.Aeson
import ZkFold.Symbolic.Interpreter (Interpreter)
import ZkFold.Base.Algebra.Basic.Field (Zp)

type KYCByteString context = ByteString 256 context

{-
>>> type Prime256_1 = 28948022309329048855892746252171976963363056481941560715954676764349967630337
>>> :{
exKYC :: KYCData (Interpreter (Zp Prime256_1))
exKYC = KYCData
  (fromConstant (1000 :: Natural))
  (fromConstant (2000 :: Natural))
  (fromConstant (3000 :: Natural))
  (fromConstant (4000 :: Natural))
:}
>>> encode exKYC
"{\"kycHash\":\"bb8\",\"kycID\":4000,\"kycType\":\"3e8\",\"kycValue\":\"7d0\"}"
-}
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
