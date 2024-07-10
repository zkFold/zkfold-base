module ZkFold.Symbolic.Ledger.Validation.PrivateInput where

import           Data.Bifunctor               (second)
import           Prelude                      hiding (Bool, Eq, all, any, filter, head, init, last, length, splitAt,
                                               tail, (&&), (*), (+), (/=), (==))

import           ZkFold.Symbolic.Data.Bool    (all, any, (&&))
import           ZkFold.Symbolic.Data.Eq      (Eq (..))
import           ZkFold.Symbolic.Data.List    (filter, init, last, (.:))
import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a private transaction input.
type PrivateInputWitness context =
    ( Transaction context
    , List context (Block context, List context (ContractId context, Transaction context))
    )

-- | Checks if the private input existed.
privateInputExisted ::
       Signature context
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputExisted bId i (wTx, wCTxs) =
    let wBlocks = fmap fst wCTxs
        blockHashes = fmap blockId wBlocks
        bIds   = bId .: init (fmap blockReference wBlocks)

    in bIds == blockHashes
    && any (== txId wTx) (fmap snd $ blockTransactionData $ last wBlocks)
    && any (== i) (txInputs wTx)

-- | Checks if the private input was not spent.
privateInputNotSpent ::
       Signature context
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputNotSpent bId i (_, wCTxs) =
    let wBlocks = fmap fst wCTxs
        blockHashes = fmap blockId wBlocks
        bIds   = bId .: init (fmap blockReference wBlocks)

        addr = txoAddress $ txiOutput i

    in bIds == blockHashes
    -- Witness data is consistent
    && all (\w -> let (b, lst) = w in filter (\(a, _) -> a == addr) (blockTransactionData b) == fmap (second txId) lst) wCTxs
    && all (all (\(_, t) -> all (/= i) $ txInputs t)) (fmap snd wCTxs)

-- | Checks if the private input is valid.
privateInputIsValid ::
       Signature context
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PrivateInputWitness context
    -- ^ The witness data for the private input.
    -> Bool context
privateInputIsValid bId i w =
       privateInputExisted bId i w
    && privateInputNotSpent bId i w
