module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, all, any, head, init, last, length, splitAt, tail, (&&),
                                               (*), (+), (/=), (==))

import           ZkFold.Symbolic.Data.Bool    (all, any, (&&))
import           ZkFold.Symbolic.Data.Eq      (Eq (..))
import           ZkFold.Symbolic.Data.List    (init, last, (.:))
import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a public transaction input.
type PublicInputWitness context = List context (Block context)

-- | Checks if the private input existed.
publicInputExisted ::
       Signature context
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PublicInputWitness context
    -- ^ The witness data for the public input.
    -> Bool context
publicInputExisted bId i w =
    let blockHashes = fmap blockId w
        bIds   = bId .: init (fmap blockReference w)
        inputs = blockPublicInputsProduced $ last w

    in bIds == blockHashes
    && any (== i) inputs

-- | Checks if the private input was not spent.
publicInputNotSpent ::
       Signature context
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PublicInputWitness context
    -- ^ The witness data for the public input.
    -> Bool context
publicInputNotSpent bId i w =
    let blockHashes = fmap blockId w
        bIds   = bId .: init (fmap blockReference w)

    in bIds == blockHashes
    && all (all (/= i) . blockPublicInputsSpent) w

-- | Checks if the public input is valid.
publicInputIsValid ::
       Signature context
    => BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PublicInputWitness context
    -- ^ The witness data for the public input.
    -> Bool context
publicInputIsValid bId i w =
       publicInputExisted bId i w
    && publicInputNotSpent bId i w
