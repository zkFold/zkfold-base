module ZkFold.Symbolic.Ledger.Validation.Update where

import           Prelude                                 hiding (Bool, Eq (..), all, length, splitAt, zip, (&&), (*),
                                                          (+), (==), (++))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Data.Conditional              (bool)
import           ZkFold.Symbolic.Data.Eq                       (Eq(..))
import           ZkFold.Symbolic.Data.List                     ((\\), (++), (.:), emptyList)
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Block       (BlockWitness)
import           ZkFold.Symbolic.Ledger.Validation.Transaction (TransactionWitness, transactionIsValid)

type UpdateWitness context = (Bridge L1ToL2 context, BlockWitness context)

bridgeToLedger :: Signature context => Bridge L1ToL2 context -> Update context -> Update context
bridgeToLedger Bridge {..} u =
   let (ins, _) = foldl (\(accIns, accC) o -> (Input (OutputRef (updateReference u) (accC + one)) o .: accIns, accC + one)) (emptyList, zero) $ bridgeL1Assets ++ bridgeL2Assets
   in u { updatePublicInputsProduced = updatePublicInputsProduced u ++ ins }

bridgeFromLedger :: Update context -> Bridge L2ToL1 context
bridgeFromLedger = undefined

applyTransaction :: Signature context => Transaction context -> TransactionWitness context -> Update context -> Update context
applyTransaction tx w u =
   let res = transactionIsValid (updateId u) tx w
       -- TODO: we only need to add public inputs from the previous updates here
       insSpent = updatePublicInputsSpent u ++ txPublicInputs tx
       insProduced = updatePublicInputsProduced u \\ txPublicInputs tx
       spendingContracts = txoAddress . txiOutput <$> txPublicInputs tx
       mintingContracts  = (\(Value s _ _) -> s) <$> txMint tx
       u' = u { updateTransactionData = updateTransactionData u ++ fmap (, txId tx) (spendingContracts ++ mintingContracts)
              , updatePublicInputsSpent = insSpent
              , updatePublicInputsProduced = insProduced
              }
   in bool u u' res

newUpdate :: Signature context => UpdateId context -> Bridge L1ToL2 context -> BlockWitness context -> Update context
newUpdate lastUpdateId bridgeIn ws =
   let u = Update { updateTransactionData = emptyList
                  , updatePublicInputsProduced = emptyList
                  , updatePublicInputsSpent = emptyList
                  , updateReference = lastUpdateId
                  }
   in foldl (\acc (tx, w) -> applyTransaction tx w acc) (bridgeToLedger bridgeIn u) ws

updateIsValid :: Signature context => UpdateId context -> Update context -> UpdateWitness context -> Bool context
updateIsValid uId u w = uncurry (newUpdate uId) w == u