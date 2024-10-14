{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Conditional where

import           Control.Applicative                (Applicative)
import           Control.Monad.Representable.Reader (Representable, mzipWithRep)
import           Data.Function                      (($))
import           Data.Traversable                   (Traversable, sequenceA)
import           Data.Type.Equality                 (type (~))
import           GHC.Generics                       (Par1 (Par1))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool          (Bool (Bool), BoolType)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.MonadCircuit       (newAssigned)

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

mzipWithMRep ::
  (Representable f, Traversable f, Applicative m) =>
  (a -> b -> m c) -> f a -> f b -> m (f c)
mzipWithMRep f x y = sequenceA (mzipWithRep f x y)

instance ( SymbolicData x, Context x ~ c, Symbolic c
         , Representable (Layout x), Traversable (Layout x)
         ) => Conditional (Bool c) x where
    bool x y (Bool b) = restore $ \s ->
      fromCircuit3F b (pieces x s) (pieces y s) $ \(Par1 c) ->
        mzipWithMRep $ \i j -> do
          i' <- newAssigned (\w -> (one - w c) * w i)
          j' <- newAssigned (\w -> w c * w j)
          newAssigned (\w -> w i' + w j')
