module ZkFold.Symbolic.Ledger.Types.Block where

import           Prelude                                  hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract    (ContractId)
import           ZkFold.Symbolic.Ledger.Types.Hash        (Hash)
import           ZkFold.Symbolic.Ledger.Types.Transaction (Transaction)

-- | Block hash.
type BlockId context = Hash context

-- | Block of transactions.
data Block context = Block
    { blockTransactions :: [(ContractId context, Transaction context)]
    -- ^ List of transactions in the block
    , blockReference    :: BlockId context
    -- ^ Reference to the previous block
    }
