{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.Accumulator where

import           Control.DeepSeq                       (NFData (..))
import           Control.Lens                          ((^.))
import           Control.Lens.Combinators              (makeLenses)
import           Data.Functor.Rep                      (Representable (..))
import           GHC.Generics
import           Prelude                               hiding (length, pi)

import           ZkFold.Base.Algebra.Basic.Class       (zero)
import           ZkFold.Base.Algebra.Basic.Number      (KnownNat, Natural, type (-))
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.AlgebraicMap (AlgebraicMap (..))
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.IVC.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.IVC.FiatShamir   (FiatShamir (FiatShamir))

-- Page 19, Accumulator instance
data AccumulatorInstance f i c k
    = AccumulatorInstance
        { _pi :: i f            -- pi ∈ M^{l_in} in the paper
        , _c  :: Vector k c     -- [C_i] ∈ C^k in the paper
        , _r  :: Vector (k-1) f -- [r_i] ∈ F^{k-1} in the paper
        , _e  :: c              -- E ∈ C in the paper
        , _mu :: f              -- μ ∈ F in the paper
        }
    deriving (Show, Generic, NFData)

makeLenses ''AccumulatorInstance

-- Page 19, Accumulator
-- @acc.x@ (accumulator instance) from the paper corresponds to _x
-- @acc.w@ (accumulator witness) from the paper corresponds to _w
data Accumulator f i m c k
    = Accumulator
        { _x :: AccumulatorInstance f i c k
        , _w :: Vector k m
        }
    deriving (Show, Generic, NFData)

makeLenses ''Accumulator

emptyAccumulator :: forall f i m c (d :: Natural) k a algo.
    ( Representable i
    , m ~ [f]
    , HomomorphicCommit m c
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    ) => FiatShamir algo (CommitOpen a) -> Accumulator f i m c k
emptyAccumulator (FiatShamir (CommitOpen sps)) =
    let accW  = tabulate (const zero)
        aiC   = fmap hcommit accW
        aiR   = tabulate (const zero)
        aiMu  = zero
        aiPI  = tabulate (const zero)
        aiE   = hcommit $ algebraicMap @_ @_ @d sps aiPI accW aiR aiMu
        accX = AccumulatorInstance { _pi = aiPI, _c = aiC, _r = aiR, _e = aiE, _mu = aiMu }
    in Accumulator accX accW

emptyAccumulatorInstance :: forall f i m c (d :: Natural) k a algo .
    ( Representable i
    , m ~ [f]
    , HomomorphicCommit m c
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    ) => FiatShamir algo (CommitOpen a) -> AccumulatorInstance f i c k
emptyAccumulatorInstance fs = emptyAccumulator @_ @_ @_ @_ @d fs ^. x
