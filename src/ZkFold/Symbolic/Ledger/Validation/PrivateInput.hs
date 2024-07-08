module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (&&), (*), (+))

import           ZkFold.Symbolic.Data.Bool    (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a private transaction input.
data PrivateInputWitness context

-- | Checks if the private input existed.
privateInputExisted ::
       BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputExisted _ _ _ = undefined

-- | Checks if the private input was not spent.
privateInputNotSpent ::
       BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputNotSpent _ _ _ = undefined

-- | Checks if the private input is valid.
privateInputIsValid ::
    BoolType (Bool context)
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputIsValid s i w = privateInputExisted s i w && privateInputNotSpent s i w
