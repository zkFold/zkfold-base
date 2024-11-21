{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Input (
    SymbolicInput (..)
) where

import           Control.DeepSeq                    (NFData)
import           Data.Functor.Rep                   (Representable)
import qualified Data.Functor.Rep              as R (Rep)
import           Data.Ord                           (Ord)
import           Data.Type.Equality                 (type (~))
import           Data.Typeable                      (Proxy (..))
import           GHC.Generics                       (Par1 (..), (:*:) (..), Generic)
import qualified GHC.Generics                  as G (Rep, from)
import           GHC.TypeLits                       (KnownNat)
import           Prelude                            (foldl, ($), (.))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative   (HApplicative)
import           ZkFold.Base.Data.ByteString        (Binary)
import           ZkFold.Base.Data.Vector            (Vector, fromVector)
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
    , Binary (R.Rep (Layout d))
    , Ord (R.Rep (Layout d))
    , NFData (R.Rep (Layout d))
    ) => SymbolicInput d where
    isValid :: d -> Bool (Context d)
    default isValid ::
      (Generic d, GSymbolicInput (G.Rep d), GContext (G.Rep d) ~ Context d)
      => d -> Bool (Context d)
    isValid = gisValid @(G.Rep d) . G.from


instance Symbolic c => SymbolicInput (Bool c) where
  isValid (Bool b) = Bool $ fromCircuitF b $
      \(Par1 v) -> do
        u <- newAssigned (\x -> x v * (one - x v))
        isZero $ Par1 u


instance
  ( Symbolic c
  , Binary (R.Rep f)
  , Ord (R.Rep f)
  , NFData (R.Rep f)
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

instance (
    Symbolic (Context x)
    , Context x ~ Context y
    , Context y ~ Context z
    , SymbolicInput x
    , SymbolicInput y
    , SymbolicInput z
    ) => SymbolicInput (x, y, z) where
  isValid (l, m, r) = isValid l && isValid m && isValid r

instance (
  Symbolic (Context x)
  , KnownNat n
  , SymbolicInput x
  ) => SymbolicInput (Vector n x) where
  isValid v = foldl (\l r -> l && isValid r) true $ fromVector v

class
    ( GSymbolicData u
    ) => GSymbolicInput u where
    gisValid :: u x -> Bool (GContext u)

instance
    ( GContext u ~ GContext v
    , GSupport u ~ GSupport v
    , HApplicative (GContext v)
    , Symbolic (GContext u)
    , GSymbolicInput u
    , GSymbolicInput v
    ) => GSymbolicInput (u :*: v) where

    gisValid (u :*: v) = gisValid u && gisValid v
