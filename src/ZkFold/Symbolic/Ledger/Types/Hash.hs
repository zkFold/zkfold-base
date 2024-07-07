module ZkFold.Symbolic.Ledger.Types.Hash where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

data Hash a

class Hashable a x where
  hash :: x -> Hash a