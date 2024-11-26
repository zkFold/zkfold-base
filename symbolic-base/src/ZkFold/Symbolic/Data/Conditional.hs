{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Conditional where

import           Control.Monad.Representable.Reader (Representable, mzipWithRep)
import           Data.Function                      (($))
import           Data.Traversable                   (Traversable)
import           Data.Type.Equality                 (type (~))
import           GHC.Generics                       (Par1 (Par1))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool          (Bool (Bool), BoolType)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators   (mzipWithMRep)
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

instance ( SymbolicData x, Context x ~ c, Symbolic c
         , Representable (Layout x), Traversable (Layout x)
         , Representable (Payload x)
         ) => Conditional (Bool c) x where
    bool x y (Bool b) = restore $ \s ->
      ( fromCircuit3F b (arithmetize x s) (arithmetize y s) $ \(Par1 c) ->
          mzipWithMRep $ \i j -> do
            i' <- newAssigned (\w -> (one - w c) * w i)
            j' <- newAssigned (\w -> w c * w j)
            newAssigned (\w -> w i' + w j')
      , let Par1 wb = witnessF b
         in mzipWithRep
              (\wx wy -> (one - wb) * wx + wb * wy)
              (payload x s)
              (payload y s)
      )
