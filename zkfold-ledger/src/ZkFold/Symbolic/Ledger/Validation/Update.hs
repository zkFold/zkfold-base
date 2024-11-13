module ZkFold.Symbolic.Ledger.Validation.Update where

import           Prelude                                       hiding (Bool, Eq (..), all, length, splitAt, zip, (&&),
                                                                (*), (+), (++), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Data.Conditional              (bool)
import           ZkFold.Symbolic.Data.Eq                       (Eq (..))
import           ZkFold.Symbolic.Data.List                     (List, emptyList, (++), (.:), (\\))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Transaction (TransactionWitness, transactionIsValid)

type UpdateWitness context = List context (Transaction context, TransactionWitness context)

-- bridgeToLedger :: Signature context => Bridge L1ToL2 context -> Update context -> Update context
-- bridgeToLedger Bridge {..} u =
--    let (ins, _) = foldl (\(accIns, accC) o -> (Input (OutputRef (updateReference u) (accC + one)) o .: accIns, accC + one)) (emptyList, zero) $ bridgeL1Assets ++ bridgeL2Assets
--    in u { updatePublicInputsProduced = updatePublicInputsProduced u ++ ins }

-- bridgeFromLedger :: Update context -> Bridge L2ToL1 context
-- bridgeFromLedger = undefined

-- applyTransaction :: Signature context => Transaction context -> TransactionWitness context -> Update context -> Update context
-- applyTransaction tx w u =
--    let res = transactionIsValid (updateId u) tx w
--       --  insSpent = (updatePublicInputsSpent u ++ txPublicInputs tx) \\ updatePublicInputsProduced u
--       --  insProduced = updatePublicInputsProduced u \\ txPublicInputs tx
--        spendingContracts = txoAddress . txiOutput <$> txInputs tx
--        mintingContracts  = (\(Value s _ _) -> s) <$> txMint tx
--        u' = u { updateTransactionData = updateTransactionData u ++ fmap (, _) (spendingContracts ++ mintingContracts)
--               -- , updatePublicInputsSpent = insSpent
--               -- , updatePublicInputsProduced = insProduced
--               }
--    in bool u u' res

-- applyTransaction :: Signature context => Transaction context -> TransactionWitness context -> Update context -> Update context
-- applyTransaction tx w u =
--    let res = transactionIsValid (updateId u) tx w
--        insSpent = (updatePublicInputsSpent u ++ txPublicInputs tx) \\ updatePublicInputsProduced u
--        insProduced = updatePublicInputsProduced u \\ txPublicInputs tx
--        spendingContracts = txoAddress . txiOutput <$> txPublicInputs tx
--        mintingContracts  = (\(Value s _ _) -> s) <$> txMint tx
--        u' = u { updateTransactionData = updateTransactionData u ++ fmap (, txId tx) (spendingContracts ++ mintingContracts)
--               , updatePublicInputsSpent = insSpent
--               , updatePublicInputsProduced = insProduced
--               }
--    in bool u u' res

-- newUpdate :: Signature context => UpdateId context -> UpdateWitness context -> Update context
-- newUpdate lastUpdateId (bridgeIn, ws) =
--    let u = Update { updateTransactionData = emptyList
--                   , updatePublicInputsProduced = emptyList
--                   , updatePublicInputsSpent = emptyList
--                   , updateReference = lastUpdateId
--                   }
--    in foldl (\acc (tx, w) -> applyTransaction tx w acc) (bridgeToLedger bridgeIn u) ws

-- updateIsValid :: Signature context => UpdateId context -> Update context -> UpdateWitness context -> Bool context
-- updateIsValid uId u w = newUpdate uId w == u
