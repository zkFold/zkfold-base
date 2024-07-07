module ZkFold.Symbolic.Ledger.Types.Hash where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

data Hash backend

class Hashable backend x where
  hash :: x -> Hash backend