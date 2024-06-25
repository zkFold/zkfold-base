module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (&&))

import           ZkFold.Base.Algebra.Basic.Class (Ring)
import           ZkFold.Symbolic.Data.Bool       (Bool, BoolType (..))
import           ZkFold.Symbolic.Ledger.Types    (Input, LedgerState)

type PrivateInputWitness a = a

privateInputExisted ::
       LedgerState a
    -> Input a
    -> PrivateInputWitness a
    -> Bool a
privateInputExisted _ _ _ = undefined

privateInputNotSpent ::
       LedgerState a
    -> Input a
    -> PrivateInputWitness a
    -> Bool a
privateInputNotSpent _ _ _ = undefined

privateInputIsValid ::
       Ring a
    => LedgerState a
    -> Input a
    -> PrivateInputWitness a -> Bool a
privateInputIsValid s i w = privateInputExisted s i w && privateInputNotSpent s i w