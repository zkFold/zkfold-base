{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Data.KYC where

import           Prelude                             hiding (Bool, Eq, length, replicate, splitAt, (*), (+))

import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize (..))
import GHC.Generics (Generic)

data KYCData context = KYCData 
    { kycType :: ByteString 256 context
    , kycValue :: ByteString 256 context
    , kycHash :: ByteString 256 context
    , kycID :: UInt 64 Auto context
    } deriving Generic



