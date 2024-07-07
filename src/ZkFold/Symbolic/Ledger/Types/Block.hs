module ZkFold.Symbolic.Ledger.Types.Block where

import           Prelude                                  hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract    (ContractId)
import           ZkFold.Symbolic.Ledger.Types.Hash        (Hash)
import           ZkFold.Symbolic.Ledger.Types.Transaction (Transaction)

type BlockId backend = Hash backend

data Block backend = Block
    { blockTransactions :: [(ContractId backend, Transaction backend)]
    , blockReference    :: BlockId backend
    }