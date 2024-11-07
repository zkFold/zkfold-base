{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.Protostar.Accumulator where

import           Control.DeepSeq          (NFData (..))
import           Control.Lens.Combinators (makeLenses)
import           GHC.Generics
import           Prelude                  hiding (length, pi)

-- Page 19, Accumulator instance
data AccumulatorInstance pi f c
    = AccumulatorInstance
        { _pi :: pi    -- pi ∈  M^{l_in} in the paper
        , _c  :: [c]   -- [C_i] ∈  C^k in the paper
        , _r  :: [f]   -- [r_i] ∈  F^{k-1} in the paper
        , _e  :: c     -- E ∈  C in the paper
        , _mu :: f     -- μ ∈  F in the paper
        }
    deriving (Show, Generic, NFData)

makeLenses ''AccumulatorInstance

-- Page 19, Accumulator
-- @acc.x@ (accumulator instance) from the paper corresponds to _x
-- @acc.w@ (accumulator witness) from the paper corresponds to _w
data Accumulator pi f c m
    = Accumulator
        { _x :: AccumulatorInstance pi f c
        , _w :: [m]
        }
    deriving (Show, Generic, NFData)

makeLenses ''Accumulator
