{-# LANGUAGE DerivingStrategies #-}
module ZkFold.Symbolic.Cardano.Data where

import qualified Data.ByteString          as BS

import           Prelude                  (Eq (..), Integer, Ord (..), Show (..))


data Data =
      Constr Integer [Data]
    | Map [(Data, Data)]
    | List [Data]
    | I Integer
    | B BS.ByteString
    deriving stock (Show, Eq, Ord)

