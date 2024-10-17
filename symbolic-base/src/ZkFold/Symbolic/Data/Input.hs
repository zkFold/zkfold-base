{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Input (
    SymbolicInput (..)
) where

import           Control.Monad.Representable.Reader (Rep)
import           Data.Functor.Rep                   (Representable)
import           Data.Ord                           (Ord)
import           Data.Type.Equality                 (type (~))
import           Data.Typeable                      (Proxy (..))
import           GHC.Generics                       (Par1 (..))
import           Prelude                            (($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString        (Binary)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.MonadCircuit


-- | A class for Symbolic input.
class
    ( SymbolicData d
    , Support d ~ Proxy (Context d)
    , Representable (Layout d)
    , Binary (Rep (Layout d))
    , Ord (Rep (Layout d))
    ) => SymbolicInput d where
    isValid :: d -> Bool (Context d)


instance Symbolic c => SymbolicInput (Bool c) where
  isValid (Bool b) = Bool $ fromCircuitF b $
      \(Par1 v) -> do
        u <- newAssigned (\x -> x v * (one - x v))
        isZero $ Par1 u


instance
  ( Symbolic c
  , Binary (Rep f)
  , Ord (Rep f)
  , Representable f) => SymbolicInput (c f) where
  isValid _ = true


instance Symbolic c => SymbolicInput (Proxy c) where
  isValid _ = true

instance (
    Symbolic (Context x)
    , Context x ~ Context y
    , SymbolicInput x
    , SymbolicInput y
    ) => SymbolicInput (x, y) where
  isValid (l, r) = isValid l && isValid r
