module ZkFold.Symbolic.Ledger.Types.Block where

import           Prelude                                  hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract    (ContractId)
import           ZkFold.Symbolic.Ledger.Types.Hash        (Hash)
import           ZkFold.Symbolic.Ledger.Types.Transaction (Transaction)

type BlockId a = Hash a

data Block uint utc a = Block
    { blockTransactions :: [(ContractId a, Transaction uint utc a)]
    , blockReference    :: BlockId a
    }