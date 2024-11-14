{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}

module ZkFold.Base.Protocol.Protostar.Accumulator where

import           Control.DeepSeq                  (NFData (..))
import           Control.Lens.Combinators         (makeLenses)
import           GHC.Generics
import           Prelude                          hiding (length, pi)

import           ZkFold.Base.Algebra.Basic.Number (type (-))
import           ZkFold.Base.Data.Vector          (Vector)

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
