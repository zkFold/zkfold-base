module ZkFold.Symbolic.Ledger.Validation.Block where

import           Data.Zip                                      (Zip(..))
import           Prelude                                       hiding (Bool, Eq(..), length, splitAt, (*), (+), (==), all, (&&), zip)

import           ZkFold.Symbolic.Data.Bool                     (BoolType(..), all)
import           ZkFold.Symbolic.Data.Eq                       (Eq(..))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Transaction

-- | Witness data that is required to prove the validity of a block.
type BlockWitness context = List context (Transaction context, TransactionWitness context)

-- | Checks if the new block is valid.
newBlockIsValid ::
      Eq (Bool context) (Hash context)
   => Eq (Bool context) (List context (ContractId context))
   => Eq (Bool context) (List context (Transaction context))
   => Zip (List context)
   => Foldable (List context)
   => BlockId context
   -- ^ The id of the current block.
   -> Block context
   -- ^ The new block to check.
   -> BlockWitness context
   -- ^ The witness data for the new block.
   -> Bool context
newBlockIsValid curBlockId Block {..} ws =
        blockReference == curBlockId
     && all (uncurry (transactionIsValid curBlockId)) ws
     && blockTransactions == fmap fst ws
