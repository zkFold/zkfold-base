{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Data.KYC where

import           Data.Foldable                       (Foldable (foldl'))
import           GHC.Generics                        (Generic)

import           ZkFold.Base.Data.Vector             (Vector, parFmap)
import           ZkFold.Symbolic.Cardano.Types.Basic (Bool, ByteString, UInt)
import           ZkFold.Symbolic.Class               (Symbolic)
import           ZkFold.Symbolic.Data.Bool           (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize (..))
import           ZkFold.Symbolic.Data.Eq             (Eq ((==)))


type KYCByteString context = ByteString 256 context

data KYCData context = KYCData
    { kycType  :: KYCByteString context
    , kycValue :: KYCByteString context
    , kycHash  :: KYCByteString context
    , kycID    :: UInt 64 Auto context
    } deriving Generic

isCitizen :: (Symbolic c) => KYCByteString c -> Vector n (KYCByteString c) -> Bool c
isCitizen citizenship allowedCountries = foldl' (||) false (parFmap (== citizenship) allowedCountries)
