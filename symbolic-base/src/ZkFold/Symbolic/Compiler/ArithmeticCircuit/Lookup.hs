{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Lookup where
import           Control.DeepSeq (NFData)
import           Data.Aeson      (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Binary     (Binary)
import           GHC.Base        (Bool (..), Eq, Ord, error)
import           GHC.Generics    (Generic)
import           GHC.Show        (Show)


data Lookup a = Range a | Tuple1 a | Tuple2 a | Tuple3 a
  deriving
    ( Generic, Binary, FromJSON, FromJSONKey, ToJSON, ToJSONKey
    , Show, Eq, Ord, NFData)


isRange :: Lookup a -> Bool
isRange l = case l of
  Range _ -> True
  _       -> False

fromRange :: Lookup a -> a
fromRange (Range a) = a
fromRange _         = error "it's not Range lookup"
