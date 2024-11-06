module ZkFold.Symbolic.Ledger.Types.Update where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract  (ContractId)
import           ZkFold.Symbolic.Ledger.Types.Hash      (Hash)
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)

-- TODO: Add contract public data to the update.

-- | Block hash of the corresponding block.
type UpdateId context = Hash context

-- | Update is a public data contained in a block.
-- TODO: This has been significantly redesigned. See the internal PDF docs.
-- Instead of "public inputs and outputs", we now have "online and offline transactions".
data Update context = Update
    { updateTransactionData      :: List context (ContractId context, TransactionId context)
    -- ^ List of contract-transaction pairs in the update
    , updatePublicInputsProduced :: List context (Input context)
    -- ^ List of public inputs produced by the update
    , updatePublicInputsSpent    :: List context (Input context)
    -- ^ List of public inputs spent by the update
    , updateReference            :: UpdateId context
    -- ^ Reference to the previous update
    }

updateId :: Update context -> UpdateId context
updateId = undefined

type UpdateChain context = List context (Update context)
