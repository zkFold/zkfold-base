{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Input (
    SymbolicInput (..)
) where

import           Control.DeepSeq                  (NFData)
import qualified Data.Functor.Rep                 as R
import           Data.Ord                         (Ord)
import           Data.Type.Equality               (type (~))
import           Data.Typeable                    (Proxy (..))
import qualified GHC.Generics                     as G
import           GHC.TypeLits                     (KnownNat)
import           Prelude                          (foldl, ($), (.))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString      (Binary)
import           ZkFold.Base.Data.Vector          (Vector, fromVector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.MonadCircuit


-- | A class for Symbolic input.
class
    ( SymbolicData d
    , Support d ~ Proxy (Context d)
    , R.Representable (Layout d)
    , Binary (R.Rep (Layout d))
    , Ord (R.Rep (Layout d))
    , NFData (R.Rep (Layout d))
    ) => SymbolicInput d where
    isValid :: d -> Bool (Context d)
    default isValid ::
      (G.Generic d, GSymbolicInput (G.Rep d), GContext (G.Rep d) ~ Context d)
      => d -> Bool (Context d)
    isValid = gisValid @(G.Rep d) . G.from


instance Symbolic c => SymbolicInput (Bool c) where
  isValid (Bool b) = Bool $ fromCircuitF b $
      \(G.Par1 v) -> do
        u <- newAssigned (\x -> x v * (one - x v))
        isZero $ G.Par1 u


instance
  ( Symbolic c
  , Binary (R.Rep f)
  , Ord (R.Rep f)
  , NFData (R.Rep f)
  , R.Representable f) => SymbolicInput (c f) where
  isValid _ = true


instance Symbolic c => SymbolicInput (Proxy c) where
  isValid _ = true

instance (
    Symbolic (Context x)
    , Context x ~ Context y
    , SymbolicInput x
    , SymbolicInput y
    ) => SymbolicInput (x, y) where

instance (
    Symbolic (Context x)
    , Context x ~ Context y
    , Context y ~ Context z
    , SymbolicInput x
    , SymbolicInput y
    , SymbolicInput z
    ) => SymbolicInput (x, y, z) where

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
    , Symbolic (GContext u)
    , GSymbolicInput u
    , GSymbolicInput v
    ) => GSymbolicInput (u G.:*: v) where
    gisValid (u G.:*: v) = gisValid u && gisValid v

instance GSymbolicInput u => GSymbolicInput (G.M1 i c u) where
    gisValid (G.M1 u) = gisValid u

instance SymbolicInput x => GSymbolicInput (G.Rec0 x) where
    gisValid (G.K1 x) = isValid x
