{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.Accumulator where

import           Control.DeepSeq                       (NFData (..), NFData1)
import           Control.Lens                          ((^.))
import           Control.Lens.Combinators              (makeLenses)
import           Data.Binary                           (Binary)
import           Data.Distributive                     (Distributive (..))
import           Data.Functor.Rep                      (Representable (..), collectRep, distributeRep)
import           GHC.Generics
import           Prelude                               hiding (length, pi)

import           ZkFold.Base.Algebra.Basic.Class       (Ring, Scale, zero)
import           ZkFold.Base.Algebra.Basic.Number      (KnownNat, type (+), type (-))
import           ZkFold.Base.Data.ByteString           (Binary1)
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.AlgebraicMap (algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.IVC.Oracle       (HashAlgorithm, RandomOracle)
import           ZkFold.Base.Protocol.IVC.Predicate    (Predicate)
import           ZkFold.Symbolic.Data.Class            (SymbolicData (..))

-- Page 19, Accumulator instance
data AccumulatorInstance k i c f
    = AccumulatorInstance
        { _pi :: i f             -- pi ∈ M^{l_in} in the paper
        , _c  :: Vector k (c f)  -- [C_i] ∈ C^k in the paper
        , _r  :: Vector (k-1) f  -- [r_i] ∈ F^{k-1} in the paper
        , _e  :: c f             -- E ∈ C in the paper
        , _mu :: f               -- μ ∈ F in the paper
        }
    deriving (Show, Eq, Generic, Generic1, NFData, NFData1, Functor, Foldable, Traversable)

makeLenses ''AccumulatorInstance

instance (KnownNat k, KnownNat (k - 1), Binary1 i, Binary1 c, Binary f) => Binary (AccumulatorInstance k i c f)

instance (Representable i, Representable c, KnownNat k, KnownNat (k-1)) => Distributive (AccumulatorInstance k i c) where
    distribute = distributeRep
    collect = collectRep

instance (Representable i, Representable c, KnownNat k, KnownNat (k-1)) => Representable (AccumulatorInstance k i c)

instance (HashAlgorithm algo f, RandomOracle algo f f, RandomOracle algo (i f) f, RandomOracle algo (c f) f)
    => RandomOracle algo (AccumulatorInstance k i c f) f

instance
    ( KnownNat (k-1)
    , KnownNat k
    , SymbolicData f
    , SymbolicData (i f)
    , SymbolicData (c f)
    , Context f ~ Context (c f)
    , Context f ~ Context (i f)
    , Support f ~ Support (c f)
    , Support f ~ Support (i f)
    ) => SymbolicData (AccumulatorInstance k i c f)

-- Page 19, Accumulator
-- @acc.x@ (accumulator instance) from the paper corresponds to _x
-- @acc.w@ (accumulator witness) from the paper corresponds to _w
data Accumulator k i c f
    = Accumulator
        { _x :: AccumulatorInstance k i c f
        , _w :: Vector k [f]
        }
    deriving (Show, Generic, NFData)

makeLenses ''Accumulator

emptyAccumulator :: forall d k a i p c f .
    ( KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Representable i
    , HomomorphicCommit [f] (c f)
    , Ring f
    , Scale a f
    ) => Predicate a i p -> Accumulator k i c f
emptyAccumulator phi =
    let accW  = tabulate (const zero)
        aiC   = fmap hcommit accW
        aiR   = tabulate (const zero)
        aiMu  = zero
        aiPI  = tabulate (const zero)
        aiE   = hcommit $ algebraicMap @d phi aiPI accW aiR aiMu
        accX = AccumulatorInstance { _pi = aiPI, _c = aiC, _r = aiR, _e = aiE, _mu = aiMu }
    in Accumulator accX accW

emptyAccumulatorInstance :: forall d k a i p c f .
    ( KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Representable i
    , HomomorphicCommit [f] (c f)
    , Ring f
    , Scale a f
    ) => Predicate a i p -> AccumulatorInstance k i c f
emptyAccumulatorInstance phi = emptyAccumulator @d phi ^. x
