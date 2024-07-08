module ZkFold.Symbolic.Ledger.Types.Hash where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

data Hash context

class Hashable context x where
  hash :: x -> Hash context