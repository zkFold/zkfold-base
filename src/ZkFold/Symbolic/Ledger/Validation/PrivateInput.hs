module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (&&))

import           ZkFold.Symbolic.Data.Bool       (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a private transaction input.
data PrivateInputWitness context

-- | Checks if the private input existed.
privateInputExisted ::
       BlockId context
    -> Input context
    -> PrivateInputWitness context
    -> Bool context
privateInputExisted _ _ _ = undefined

-- | Checks if the private input was not spent.
privateInputNotSpent ::
       BlockId context
    -> Input context
    -> PrivateInputWitness context
    -> Bool context
privateInputNotSpent _ _ _ = undefined

-- | Checks if the private input is valid.
privateInputIsValid ::
    BoolType (Bool context)
    => BlockId context
    -> Input context
    -> PrivateInputWitness context
    -> Bool context
privateInputIsValid s i w = privateInputExisted s i w && privateInputNotSpent s i w