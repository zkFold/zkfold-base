module ZkFold.Symbolic.Ledger.Types.Value where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

-- | Input to the minting contract. Usually a token name.
data Token context

-- | A minting contract is a contract that guards the minting and burning of tokens.
-- In order to mint or burn tokens, the transaction must satisfy the minting contract.
type MintingContract tx w context = Contract tx (Token context) w context

-- | A value represents the amount of tokens that is contained in a transaction output.
-- The `ContractId` corresponds to the contract that minted the tokens with the `Token` containing the input data.
-- The `UInt64` contains the amount of tokens.
data Value context = Value (ContractId context) (Token context) (UInt64 context)
