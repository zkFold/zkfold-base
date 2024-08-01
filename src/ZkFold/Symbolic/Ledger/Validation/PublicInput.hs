module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                                  hiding (Bool, Eq, all, any, head, init, last, length, splitAt, tail, (&&),
                                                            (*), (+), (/=), (==))

import           ZkFold.Symbolic.Data.Bool                (all, any, (&&))
import           ZkFold.Symbolic.Data.Eq                  (Eq (..))
import           ZkFold.Symbolic.Data.List                (last, head)
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Common (updateChainIsValid)

-- | Witness data that is required to prove the validity of a public transaction input.
type PublicInputWitness context = UpdateChain context

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
    let u      = head w
        u0     = last w
        inputs = updatePublicInputsProduced u0

    in updateChainIsValid w
    -- ^ The update chain is valid
    && updateId u == bId
    -- ^ The most recent update is the current block
    && any (== i) inputs
    -- ^ The input is included in the least recent update in the chain

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
    let u      = head w

    in updateChainIsValid w
    -- ^ The update chain is valid
    && updateId u == bId
    -- ^ The most recent update is the current block
    && all (all (/= i) . updatePublicInputsSpent) w
    -- ^ The input is not spent in any of the updates in the chain

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
