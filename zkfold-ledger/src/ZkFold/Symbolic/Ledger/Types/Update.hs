module ZkFold.Symbolic.Ledger.Types.Update where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.Bool              (Bool)
import           ZkFold.Symbolic.Data.Combinators       (RegisterSize(Auto))
import           ZkFold.Symbolic.Data.List              (List)
import           ZkFold.Symbolic.Data.UInt              (UInt)
import           ZkFold.Symbolic.Ledger.Types.Contract  (ContractData, ContractId)
import           ZkFold.Symbolic.Ledger.Types.Hash      (Hash)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)

-- TODO: Add contract public data to the update.

-- | Block hash of the corresponding block.
type UpdateId = Hash

type AddressIndex = UInt 40 Auto

data Update context = Update
  { updateNewAssignments :: List context (ContractId context, AddressIndex context)
    -- ^ the map from addresses into assigned indices. Only new assignments.
  , updateSpentOutputs   :: List context (AddressIndex context, Bool context)
    -- ^ the map from address indices into boolean values.
    -- The keys are all indices of addresses from which an output was spent in the update.
    -- The boolean values indicate whether the transactions that spent outputs from a particular address should be included in the Update.
  , updateTransactions   :: List context (AddressIndex context, TransactionId context)
    -- ^ the map from address indices into transaction id lists. Contains offline transactions.
  , updateTransactionData :: List context (AddressIndex context, ContractData context)
    -- ^ the map from address indices into the accumulated public data items. Only non-empty public data.
  }

updateId :: Update context -> UpdateId context
updateId = undefined

type UpdateChain context = List context (Update context)
