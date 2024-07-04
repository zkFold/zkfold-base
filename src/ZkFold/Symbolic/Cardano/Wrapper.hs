module ZkFold.Symbolic.Cardano.Wrapper where

import           Prelude                                   hiding (Bool, Eq (..), length, splitAt, (&&), (*), (+))

import           ZkFold.Symbolic.Cardano.Types.Transaction (Transaction)
import           ZkFold.Symbolic.Data.Bool                 (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Eq                   (Eq ((==)))
import           ZkFold.Symbolic.Data.UInt                 (UInt)

type TxHash b a = UInt 64 b a

-- TODO: implement transaction hashing
hashFunction :: Transaction inputs rinputs outputs tokens datum b a -> TxHash b a
hashFunction = undefined -- from . blake2b_224 . serialiseData . toBuiltinData

type Contract tx redeemer backend a = tx backend a -> redeemer backend a -> Bool a

-- | Use wrapper to convert circuit to plonk circuit
symbolicContractWrapper :: forall inputs rinputs outputs tokens datum redeemer backend a .
    Eq (Bool a) (UInt 64 backend a)
    => Contract (Transaction inputs rinputs outputs tokens datum) redeemer backend a
    -> TxHash backend a
    -> Transaction inputs rinputs outputs tokens datum backend a
    -> redeemer backend a
    -> Bool a
symbolicContractWrapper contract hash tx witness =
    let -- Сhecking the supplied hash
        conditionCorrectHash      = hashFunction tx == hash :: Bool a

        -- Run the contract on one public and several private inputs
        conditionContractSucceeds = contract tx witness

    in conditionCorrectHash && conditionContractSucceeds
