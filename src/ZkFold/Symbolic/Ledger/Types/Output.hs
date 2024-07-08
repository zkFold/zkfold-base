module ZkFold.Symbolic.Ledger.Types.Output where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Value   (Value)
import           ZkFold.Symbolic.Ledger.Types.Address (Address, Datum)

data Output context = Output
        { txoAddress  :: Address context
        , txoValue    :: Value context
        , txoDatum    :: Datum context
}