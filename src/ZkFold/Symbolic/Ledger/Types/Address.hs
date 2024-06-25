module ZkFold.Symbolic.Ledger.Types.Address where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract (Contract)

type Datum a = [a]

data Address a where
    Address :: Contract tx (Datum a) w a -> w -> Address a