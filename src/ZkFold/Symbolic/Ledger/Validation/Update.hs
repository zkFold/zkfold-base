module ZkFold.Symbolic.Ledger.Validation.Update where

import           Prelude                                 hiding (Bool, Eq (..), all, length, splitAt, zip, (&&),
                                                            (*), (+), (==))

import           ZkFold.Symbolic.Data.Bool               (BoolType(..))
import           ZkFold.Symbolic.Data.Eq                 (Eq(..))
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Block (BlockWitness, newBlockIsValid)
import           ZkFold.Symbolic.Ledger.Validation.Bridge (bridgeIsValid)

type UpdateWitness context = (Block context, BlockWitness context)

-- TODO: Check that public inputs spent and produced are correct.

-- | Check if a new update is valid given the latest valid update.
newUpdateIsValid ::
      Signature context
   => Bridge L1ToL2 context
   -- ^ The bridged outputs from L1 to L2.
   -> Bridge L2ToL1 context
   -- ^ The bridged outputs from L2 to L1.
   -> UpdateId context
   -- ^ The id of the latest valid update.
   -> Update context
   -- ^ The new update to check.
   -> UpdateWitness context
   -- ^ The witness data for the new update.
   -> Bool context
newUpdateIsValid bridgeIn bridgeOut lastUpdateId u@Update {..} (wBlock, wBlockWitness) =
      lastUpdateId == updateReference
   && newBlockIsValid lastUpdateId wBlock wBlockWitness
   && bridgeIsValid bridgeIn bridgeOut u