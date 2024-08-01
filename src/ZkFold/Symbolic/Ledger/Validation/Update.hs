module ZkFold.Symbolic.Ledger.Validation.Update where

import           Prelude                                 hiding (Bool, Eq (..), all, length, splitAt, zip, (&&), (*),
                                                          (+), (==))

import           ZkFold.Symbolic.Data.Bool               (BoolType (..))
import           ZkFold.Symbolic.Data.Eq                 (Eq (..))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Block (BlockWitness, newBlockIsValid)

type UpdateWitness context = (Block context, BlockWitness context)

-- | Check if a new update is valid given the latest valid update.
newUpdateIsValid ::
      Signature context
   => UpdateId context
   -- ^ The id of the latest valid update.
   -> Update context
   -- ^ The new update to check.
   -> UpdateWitness context
   -- ^ The witness data for the new update.
   -> Bool context
newUpdateIsValid lastUpdateId Update {..} (wBlock, wBlockWitness) =
      lastUpdateId == updateReference
   && newBlockIsValid lastUpdateId wBlock wBlockWitness
