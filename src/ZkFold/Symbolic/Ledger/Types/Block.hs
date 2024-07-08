module ZkFold.Symbolic.Ledger.Types.Block where

import           Prelude                                  hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract    (ContractId)
import           ZkFold.Symbolic.Ledger.Types.Hash        (Hash)
import           ZkFold.Symbolic.Ledger.Types.Transaction (Transaction)

type BlockId context = Hash context

data Block context = Block
    { blockTransactions :: [(ContractId context, Transaction context)]
    , blockReference    :: BlockId context
    }