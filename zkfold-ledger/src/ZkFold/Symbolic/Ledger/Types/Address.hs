module ZkFold.Symbolic.Ledger.Types.Address where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement)

-- | Input to the spending contract. Usually some sort of commitment information to be used when spending the output.
type Datum = FieldElement

-- | A contract that locks a transaction output.
-- In order to spend the output, the spending transaction must satisfy the contract.
type SpendingContract tx w context = Contract tx (Datum context) w context

-- | Address on the zkFold ledger.
type Address context = ContractId context
