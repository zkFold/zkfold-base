{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Data.KYC where

import ZkFold.Symbolic.Cardano.Types.Basic
    ( ByteString, UInt, Bool )
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize (..))
import GHC.Generics (Generic)
import ZkFold.Symbolic.Class (Symbolic)
import ZkFold.Symbolic.Data.Bool (BoolType(..))
import ZkFold.Base.Data.Vector ( parFmap, Vector )
import ZkFold.Symbolic.Data.Eq ( Eq((==)) )
import Data.Foldable ( Foldable(foldl') ) 


type KYCByteString context = ByteString 256 context

data KYCData context = KYCData 
    { kycType :: KYCByteString context
    , kycValue :: KYCByteString context
    , kycHash :: KYCByteString context
    , kycID :: UInt 64 Auto context
    } deriving Generic

isCitizen :: (Symbolic c) => KYCByteString c -> Vector n (KYCByteString c) -> Bool c
isCitizen citizenship allowedCountries = foldl' (||) false (parFmap (== citizenship) allowedCountries)
