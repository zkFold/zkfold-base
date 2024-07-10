module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                                    hiding (Bool, Eq, length, splitAt, (&&), (*), (+), (==), (++), all, sum)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Data.Bool                  (BoolType (..), all)
import           ZkFold.Symbolic.Data.Eq                    (Eq(..))
import           ZkFold.Symbolic.Data.List                  ((++))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Contract

-- | Witness data for the inputs of a transaction.
data TransactionInputsWitness context

-- | Witness data for a transaction satisfies the included contracts.
type TransactionContractsWitness context = List context (ContractId context, ContractWitness context)

-- | Witness data for a transaction.
type TransactionWitness context = (TransactionInputsWitness context, TransactionContractsWitness context)

-- | Checks if the inputs of a transaction are valid.
transactionInputsAreValid ::
      BlockId context
   -- ^ The id of the current block.
   -> Transaction context
   -- ^ The transaction to check.
   -> TransactionInputsWitness context
   -- ^ The witness data for the inputs of the transaction.
   -> Bool context
transactionInputsAreValid _ _ _ = undefined

-- | Checks if the balance of a transaction is correct.
transactionBalanceIsCorrect ::
      Signature context
   => Transaction context
   -> Bool context
transactionBalanceIsCorrect tx =
   let spending  = sum (txoValue . txiOutput <$> txInputs tx)
       minting   = sum $ txMint tx
       producing = sum $ txoValue <$> txOutputs tx
   in producing == spending + minting

-- | Checks if a transaction satisfies the included contracts.
-- TODO: make sure that contracts are supplied with the correct public inputs.
transactionContractsAreSatisfied ::
      Signature context
   => Transaction context
   -> TransactionContractsWitness context
   -> Bool context
transactionContractsAreSatisfied tx ws =
   let spendingContracts = txoAddress . txiOutput <$> txInputs tx
       mintingContracts = (\(Value cId _ _) -> cId) <$> txMint tx
       contracts = spendingContracts ++ mintingContracts
   in all (uncurry $ contractIsSatisfied tx) ws
   && contracts == fmap fst ws

-- | Checks if a transaction is valid.
transactionIsValid ::
      Signature context
   => BlockId context
   -- ^ The id of the current block.
   -> Transaction context
   -- ^ The transaction to check.
   -> TransactionWitness context
   -- ^ The witness data for the inputs of the transaction.
   -> Bool context
transactionIsValid blockId tx (wInputs, wContracts) =
       transactionInputsAreValid blockId tx wInputs
    && transactionBalanceIsCorrect tx
    && transactionContractsAreSatisfied tx wContracts
