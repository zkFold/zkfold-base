module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (&&))

import           ZkFold.Symbolic.Data.Bool       (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

data PrivateInputWitness context

privateInputExisted ::
       BlockId context
    -> Input context
    -> PrivateInputWitness context
    -> Bool context
privateInputExisted _ _ _ = undefined

privateInputNotSpent ::
       BlockId context
    -> Input context
    -> PrivateInputWitness context
    -> Bool context
privateInputNotSpent _ _ _ = undefined

privateInputIsValid ::
    BoolType (Bool context)
    => BlockId context
    -> Input context
    -> PrivateInputWitness context
    -> Bool context
privateInputIsValid s i w = privateInputExisted s i w && privateInputNotSpent s i w