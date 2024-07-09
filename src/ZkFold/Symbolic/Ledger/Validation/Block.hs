module ZkFold.Symbolic.Ledger.Validation.Block where

import           Prelude                                       hiding (Bool, Eq(..), length, splitAt, (*), (+), (==), all, (&&))

import           ZkFold.Symbolic.Data.Bool                     (BoolType(..), all)
import           ZkFold.Symbolic.Data.Eq                       (Eq(..))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Transaction

-- | Witness data that is required to prove the validity of a block.
type BlockWitness context = [TransactionWitness context]

-- | Checks if the new block is valid.
newBlockIsValid ::
       Eq (Bool context) (Hash context)
    => BlockId context
    -- ^ The id of the current block.
    -> Block context
    -- ^ The new block to check.
    -> BlockWitness context
    -- ^ The witness data for the new block.
    -> Bool context
newBlockIsValid curBlockId Block {..} w =
        blockReference == curBlockId
        -- TODO: what if the list lengths are different?
     && all (uncurry (transactionIsValid curBlockId)) (zip blockTransactions w)
