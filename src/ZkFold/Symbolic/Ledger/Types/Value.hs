module ZkFold.Symbolic.Ledger.Types.Value where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Ledger.Types.Contract (Contract)

type Token a = [a]

data Policy a where
    Policy :: Contract tx (Token a) w a -> w -> Policy a

data Value a = Value (Policy a) (Token a) (UInt 64 a)