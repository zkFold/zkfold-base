module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Prelude                                  hiding (Bool, Eq, all, any, filter, head, init, last, length,
                                                           splitAt, tail, (&&), (*), (+), (/=), (==))

import           ZkFold.Symbolic.Data.Bool                (Bool, all, any, (&&))
import           ZkFold.Symbolic.Data.Eq                  (Eq (..))
import           ZkFold.Symbolic.Data.List                (List, emptyList, filter, head, last, (.:))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Common (updateChainIsValid)

-- | Witness data that is required to prove the validity of a private transaction input.
type PrivateInputWitness context =
    ( Transaction context
    , List context (Update context, List context (Transaction context))
    )

-- | Checks if the private input existed.
privateInputExisted ::
       Signature context
    => UpdateId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputExisted bId i (wTx, wCTxs) =
    let wUpdates = fmap fst wCTxs
        u        = head wUpdates
        u0       = last wUpdates
        o        = txiOutput i

    in updateChainIsValid wUpdates
    -- ^ The update chain is valid
    && updateId u == bId
    -- ^ The most recent update is the current block
    && any (== txId wTx) (fst <$> updateNewAssignments u0)
    -- ^ The transaction is included in the least recent update in the chain
    && any (== o) (txOutputs wTx)
    -- ^ The output of the transaction is the same as the input to check

-- | Checks if the private input was not spent.
privateInputNotSpent ::
       Signature context
    => UpdateId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputNotSpent bId i (_, wCTxs) =
    let wUpdates  = fmap fst wCTxs
        u         = head wUpdates

        -- Get the transaction ids for a particular contract id from the update
        txIds upd = fst <$> filter (\(cId, _) -> cId == addr) (updateNewAssignments upd)
        -- Transactions in each update
        txs       = fmap snd wCTxs

        addr = txoAddress $ txiOutput i

    in updateChainIsValid wUpdates
    -- ^ The update chain is valid
    && updateId u == bId
    -- ^ The most recent update is the current block
    && foldl (flip (.:)) emptyList (txIds <$> wUpdates) == fmap (fmap txId) txs
    -- ^ The witness data is consistent
    && all (all (all (/= i) . txInputs)) txs
    -- ^ The input is not spent in any of the contract transactions

-- | Checks if the private input is valid.
privateInputIsValid ::
       Signature context
    => UpdateId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputIsValid bId i w =
       privateInputExisted bId i w
    && privateInputNotSpent bId i w
