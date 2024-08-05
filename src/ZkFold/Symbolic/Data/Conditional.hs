module ZkFold.Symbolic.Data.Conditional where

import           Data.Function                   (($))
import           GHC.Generics                    (Par1 (Par1))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector         (zipWithM)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool       (Bool (Bool), BoolType)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.MonadCircuit    (newAssigned)

class BoolType b => Conditional b a where
    -- | Properties:
    --
    -- [On true] @bool onFalse onTrue 'true' == onTrue@
    --
    -- [On false] @bool onFalse onTrue 'false' == onFalse@
    bool :: a -> a -> b -> a

gif :: Conditional b a => b -> a -> a -> a
gif b x y = bool y x b

(?) :: Conditional b a => b -> a -> a -> a
(?) = gif

instance (Symbolic c, SymbolicData c x) => Conditional (Bool c) x where
    bool x y (Bool b) =
      restore $ \s -> fromCircuit3F b (pieces x s) (pieces y s) $ \(Par1 c) ->
          zipWithM $ \i j -> newAssigned $ \w -> w c * (w j - w i) + w i
                                          -- ^ Is this really Plonk constraint?
