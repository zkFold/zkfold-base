{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.Accumulator where

import           Control.DeepSeq                       (NFData (..))
import           Control.Lens                          ((^.))
import           Control.Lens.Combinators              (makeLenses)
import           Data.Distributive                     (Distributive (..))
import           Data.Functor.Rep                      (Representable (..), distributeRep, collectRep)
import           GHC.Generics
import           Prelude                               hiding (length, pi)

import           ZkFold.Base.Algebra.Basic.Class       (Ring, Scale, zero)
import           ZkFold.Base.Algebra.Basic.Number      (KnownNat, type (-), type (+))
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.AlgebraicMap (algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.IVC.Predicate    (Predicate)

-- Page 19, Accumulator instance
data AccumulatorInstance k i c f
    = AccumulatorInstance
        { _pi :: i f             -- pi ∈ M^{l_in} in the paper
        , _c  :: Vector k (c f)  -- [C_i] ∈ C^k in the paper
        , _r  :: Vector (k-1) f  -- [r_i] ∈ F^{k-1} in the paper
        , _e  :: c f             -- E ∈ C in the paper
        , _mu :: f               -- μ ∈ F in the paper
        }
    deriving (Show, Eq, Generic, Generic1, NFData, Functor)

instance (Representable i, Representable c, KnownNat k, KnownNat (k-1)) => Distributive (AccumulatorInstance k i c) where
    distribute = distributeRep

    collect = collectRep

deriving instance (Representable i, Representable c, KnownNat k, KnownNat (k-1)) => Representable (AccumulatorInstance k i c)

makeLenses ''AccumulatorInstance

-- Page 19, Accumulator
-- @acc.x@ (accumulator instance) from the paper corresponds to _x
-- @acc.w@ (accumulator witness) from the paper corresponds to _w
data Accumulator k i c m f
    = Accumulator
        { _x :: AccumulatorInstance k i c f
        , _w :: Vector k m
        }
    deriving (Show, Generic, NFData)

makeLenses ''Accumulator

emptyAccumulator :: forall d k a i p c m f .
    ( KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Representable i
    , HomomorphicCommit m (c f)
    , m ~ [f]    
    , Ring f
    , Scale a f
    ) => Predicate a i p -> Accumulator k i c m f
emptyAccumulator phi =
    let accW  = tabulate (const zero)
        aiC   = fmap hcommit accW
        aiR   = tabulate (const zero)
        aiMu  = zero
        aiPI  = tabulate (const zero)
        aiE   = hcommit $ algebraicMap @d phi aiPI accW aiR aiMu
        accX = AccumulatorInstance { _pi = aiPI, _c = aiC, _r = aiR, _e = aiE, _mu = aiMu }
    in Accumulator accX accW

emptyAccumulatorInstance :: forall d k a i p c m f .
    ( KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Representable i
    , HomomorphicCommit m (c f)
    , m ~ [f]    
    , Ring f
    , Scale a f
    ) => Predicate a i p -> AccumulatorInstance k i c f
emptyAccumulatorInstance phi = emptyAccumulator @d phi ^. x
