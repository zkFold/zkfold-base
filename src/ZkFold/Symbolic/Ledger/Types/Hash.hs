module ZkFold.Symbolic.Ledger.Types.Hash where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

class LedgerHash x y where
  ledgerHash :: x -> y

instance LedgerHash [a] a where
  ledgerHash = undefined