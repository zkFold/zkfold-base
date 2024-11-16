module ZkFold.Symbolic.Ledger.Validation.Update where

import           Control.Arrow                                 ((&&&))
import           Prelude                                       hiding (Bool, Eq (..), all, length, splitAt, zip, (&&),
                                                                (*), (+), (++), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Data.Bool                     (Bool)
import           ZkFold.Symbolic.Data.Class                    (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional              (bool)
import           ZkFold.Symbolic.Data.Eq                       (Eq (..))
import           ZkFold.Symbolic.Data.List                     (List, emptyList, (++), (.:), (\\))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Transaction (TransactionWitness, transactionIsValid)

type UpdateWitness context = List context (Transaction context, TransactionWitness context)

applyTransaction :: Signature context => Transaction context -> TransactionWitness context -> Update context -> Update context
applyTransaction tx w u =
   let res = transactionIsValid (updateId u) tx w
      --  insSpent = (updatePublicInputsSpent u ++ txPublicInputs tx) \\ updatePublicInputsProduced u
      --  insProduced = updatePublicInputsProduced u \\ txPublicInputs tx
       spendingContracts = (getAddressIndex &&& txoAddress . txiOutput) <$> txInputs tx
       mintingContracts  = (\(Value s _ _) -> (undefined,s)) <$> txMint tx
                                               -- ^ address index?
       pairTx addr = (getAddressIndex addr, txId tx)
       u' = u { updateTransactions = updateTransactions u ++ spendingContracts ++ mintingContracts
              -- , updatePublicInputsSpent = insSpent
              -- , updatePublicInputsProduced = insProduced
              , updateSpentOutputs = updateSpentOutputs u ++ undefined
                                        -- new spent outputs from tx ^
              }
   in bool u u' res

newUpdate :: Signature context => Hash context -> UpdateWitness context -> Update context
newUpdate lastUpdateId updWitness = undefined
  --  let u = Update { updateOnlineTxsRoot = lastUpdateId
  --                 , updateNewAssignments = emptyList
  --                 , updateSpentOutputs = emptyList
  --                 , updateTransactions = emptyList
  --                 , updateTransactionData = emptyList
  --                 , updateIndicesReleased = emptyList
  --                 , updateBridgedOutputs = emptyList
  --                 , updateBridgedInputs = emptyList
  --                 }
  --  in foldl (\acc (tx, w) -> applyTransaction tx w acc) u updWitness

updateIsValid :: Signature context => Hash context -> Update context -> UpdateWitness context -> Bool context
updateIsValid uId u w = newUpdate uId w == u
