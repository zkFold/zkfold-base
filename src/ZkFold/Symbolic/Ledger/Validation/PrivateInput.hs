module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (&&))

import           ZkFold.Symbolic.Data.Bool       (Bool, BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

type PrivateInputWitness a = a

privateInputExisted ::
       BlockId a
    -> Input uint a
    -> PrivateInputWitness a
    -> Bool a
privateInputExisted _ _ _ = undefined

privateInputNotSpent ::
       BlockId a
    -> Input uint a
    -> PrivateInputWitness a
    -> Bool a
privateInputNotSpent _ _ _ = undefined

privateInputIsValid ::
    BoolType (Bool a)
    => BlockId a
    -> Input uint a
    -> PrivateInputWitness a
    -> Bool a
privateInputIsValid s i w = privateInputExisted s i w && privateInputNotSpent s i w