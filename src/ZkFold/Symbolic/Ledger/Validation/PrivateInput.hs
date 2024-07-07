module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (&&))

import           ZkFold.Symbolic.Data.Bool       (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

data PrivateInputWitness backend

privateInputExisted ::
       BlockId backend
    -> Input backend
    -> PrivateInputWitness backend
    -> Bool backend
privateInputExisted _ _ _ = undefined

privateInputNotSpent ::
       BlockId backend
    -> Input backend
    -> PrivateInputWitness backend
    -> Bool backend
privateInputNotSpent _ _ _ = undefined

privateInputIsValid ::
    BoolType (Bool backend)
    => BlockId backend
    -> Input backend
    -> PrivateInputWitness backend
    -> Bool backend
privateInputIsValid s i w = privateInputExisted s i w && privateInputNotSpent s i w