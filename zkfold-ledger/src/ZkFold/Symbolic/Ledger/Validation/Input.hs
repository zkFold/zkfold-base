module ZkFold.Symbolic.Ledger.Validation.Input where

import           Prelude                                  hiding (Bool, Eq, Maybe, all, any, filter, head, init, last,
                                                           length, maybe, splitAt, tail, (&&), (*), (+), (/=), (==))

import           ZkFold.Symbolic.Data.Bool                (Bool, all, any, false, (&&))
import           ZkFold.Symbolic.Data.Eq                  (Eq (..))
import           ZkFold.Symbolic.Data.List                (List, emptyList, filter, findList, head, last, (.:))
import           ZkFold.Symbolic.Data.Maybe               (maybe)
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Common (updateChainIsValid)

-- | Witness data that is required to prove the validity of an input.
data InputWitness context
  = OfflineTxInputWitness
      (Transaction context)
      (List context (Update context, List context (Transaction context)))
      (Update context)
  | OnlineTxInputWitness
  | BridgedTxInputWitness

-- | Checks if the input existed.
inputExisted ::
       Signature context
    => Hash context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> InputWitness context
    -- ^ The witness data for the input.
    -> Bool context
inputExisted bId i (OfflineTxInputWitness wTx wCTxs _) =
    let wUpdates = fmap fst wCTxs
        u        = head wUpdates
        u0       = last wUpdates
        o        = txiOutput i

    in updateChainIsValid wUpdates
    -- ^ The update chain is valid
    && updateId u == bId
    -- ^ The most recent update is the current block
    && any (== txId wTx) (snd <$> updateTransactions u0)
    -- ^ The transaction is included in the least recent update in the chain
    && any (== o) (txOutputs wTx)
    -- ^ The output of the transaction is the same as the input to check

-- | Checks if the input was not spent.
inputNotSpent ::
       (Signature context, Eq (Bool context) (AddressIndex context))
    => Hash context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> InputWitness context
    -- ^ The witness data for the offline input.
    -> Bool context
inputNotSpent bId i (OfflineTxInputWitness _ wCTxs upd) =
    let wUpdates    = fmap fst wCTxs
        u           = head wUpdates
        inputAddr   = txoAddress $ txiOutput i
        -- Get the new assigned index for the input address, maybe
        addrIxMaybe = findList (\(addr, _ix) -> addr == inputAddr) (updateNewAssignments upd)
        validAddrIx (_addr, addrIx) =
          let

              -- Get the transaction ids for a particular contract id from the update
              txIds upd' = snd <$> filter (\(cId, _) -> cId == addrIx) (updateTransactions upd')
              -- Transactions in each update
              txs       = fmap snd wCTxs

          in updateChainIsValid wUpdates
          -- ^ The update chain is valid
          && updateId u == bId
          -- ^ The most recent update is the current block
          && foldl (flip (.:)) emptyList (txIds <$> wUpdates) == fmap (fmap txId) txs
          -- ^ The witness data is consistent
          && all (all (all (/= i) . txInputs)) txs
          -- ^ The input is not spent in any of the contract transactions
    in maybe false validAddrIx addrIxMaybe

-- | Checks if the input is valid.
inputIsValid ::
       (Signature context,  Eq (Bool context) (AddressIndex context))
    => Hash context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> InputWitness context
    -- ^ The witness data for the offline input.
    -> Bool context
inputIsValid bId i w =
       inputExisted bId i w
    && inputNotSpent bId i w
