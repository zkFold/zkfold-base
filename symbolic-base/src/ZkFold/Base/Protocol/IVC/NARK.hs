{-# LANGUAGE DeriveAnyClass      #-}

module ZkFold.Base.Protocol.IVC.NARK where

import           Control.DeepSeq                       (NFData (..))
import           Data.Zip                              (unzip)
import           GHC.Generics
import           Prelude                               hiding (head, length, pi, unzip)

import           ZkFold.Base.Algebra.Basic.Class       (Ring, zero)
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.FiatShamir   (FiatShamir)
import           ZkFold.Base.Protocol.IVC.SpecialSound (SpecialSoundProtocol (..))

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof k c m f
    = NARKProof
        { narkCommits :: Vector k (c f) -- Commits [C_i] ∈  C^k
        , narkWitness :: Vector k m     -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Show, Generic, NFData)

narkProof :: Ring f
    => FiatShamir k i p c m o f
    -> i f
    -> p f
    -> NARKProof k c m f
narkProof a pi0 w =
    let (ms, cs) = unzip $ prover a pi0 w zero 0
    in NARKProof cs ms

data NARKInstanceProof k i c m f = NARKInstanceProof (i f) (NARKProof k c m f)
    deriving (Show, Generic, NFData)

narkInstanceProof :: Ring f
    => FiatShamir k i p c m o f
    -> i f
    -> p f
    -> NARKInstanceProof k i c m f
narkInstanceProof a pi0 w = NARKInstanceProof (input a pi0 w) (narkProof a pi0 w)
