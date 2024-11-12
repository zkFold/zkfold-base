module ZkFold.Symbolic.Ledger.Validation.OfflineInput where

import           Data.Functor.Rep                         (Representable)
import           Prelude                                  hiding (Bool, Eq, Maybe, all, any, filter, head, init, last, length, maybe,
                                                           splitAt, tail, (&&), (*), (+), (/=), (==))

import           ZkFold.Symbolic.Class                    (Symbolic)
import           ZkFold.Symbolic.Data.Bool                (Bool, all, any, (&&), false)
import           ZkFold.Symbolic.Data.Class               (SymbolicData (Layout))
import           ZkFold.Symbolic.Data.Eq                  (Eq (..))
import           ZkFold.Symbolic.Data.List                (List, emptyList, filter, findList, head, last, (.:))
import           ZkFold.Symbolic.Data.Maybe               (Maybe, maybe)
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Common (updateChainIsValid)

-- | Witness data that is required to prove the validity of a transaction input
-- from an offline transaction output.
type OfflineInputWitness context =
    ( Transaction context
    , List context (Update context, List context (Transaction context))
    , Update context
    )

-- | Checks if the offline input existed.
offlineInputExisted ::
       Signature context
    => Hash context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> OfflineInputWitness context
    -- ^ The witness data for the input.
    -> Bool context
offlineInputExisted bId i (wTx, wCTxs, _) =
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

-- | Checks if the transaction input from on offline transaction output was not spent.
offlineInputNotSpent ::
       (Signature context, Representable (Layout (Hash context)), Eq (Bool context) (AddressIndex context))
    => Hash context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> OfflineInputWitness context
    -- ^ The witness data for the offline input.
    -> Bool context
offlineInputNotSpent bId i (_, wCTxs, upd) =
    let wUpdates    = fmap fst wCTxs
        u           = head wUpdates
        addr        = txoAddress $ txiOutput i
        -- Get the new assigned index for the input address, maybe
        addrIxMaybe = findList (\(addrK, _ix) -> addr == addrK) (updateNewAssignments upd)
        validAddrIx (_addr, addrIx) =
          let

              -- Get the transaction ids for a particular contract id from the update
              txIds upd = snd <$> filter (\(cId, _) -> cId == addrIx) (updateTransactions upd)
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
    in maybe false validAddrIx addrIxMaybe

-- | Checks if the offline input is valid.
offlineInputIsValid ::
       (Signature context, Representable (Layout (Hash context)), Symbolic context, Eq (Bool context) (AddressIndex context))
    => Hash context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> OfflineInputWitness context
    -- ^ The witness data for the offline input.
    -> Bool context
offlineInputIsValid bId i w =
       offlineInputExisted bId i w
    && offlineInputNotSpent bId i w
