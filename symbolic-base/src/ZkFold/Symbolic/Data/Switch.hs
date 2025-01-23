module ZkFold.Symbolic.Data.Switch where

import           Data.Function                    (const, ($), (.))
import           Data.Proxy                       (Proxy (..))

import           ZkFold.Symbolic.Class            (Symbolic (..))
import           ZkFold.Symbolic.Data.Bool        (Bool)
import           ZkFold.Symbolic.Data.Class       (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional (Conditional (..))
import           ZkFold.Symbolic.Data.Payloaded   (Payloaded (..))

data Switch c x = Switch
  { sLayout  :: c (Layout x)
  , sPayload :: Payload x (WitnessField c)
  }

instance (Symbolic c, SymbolicData x) => SymbolicData (Switch c x) where
  type Context (Switch c x) = c
  type Support (Switch c x) = Proxy c
  type Layout (Switch c x) = Layout x
  type Payload (Switch c x) = Payload x
  arithmetize = const . sLayout
  payload = const . sPayload
  restore f = let (sLayout, sPayload) = f Proxy in Switch {..}

instance (Symbolic c, SymbolicData x) => Conditional (Bool c) (Switch c x) where
  bool (Switch fl fp) (Switch tl tp) b =
    Switch (bool fl tl b) $ runPayloaded $
      bool (Payloaded fp :: Payloaded (Payload x) c) (Payloaded tp) b
