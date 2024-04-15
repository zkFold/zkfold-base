module ZkFold.Symbolic.Algorithms.Hash.MiMC (mimcHash) where

import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Eq (..), Num (..), any, not, (!!), (/), (^),
                                                                 (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                 ((!!))
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Data.Conditional               (bool)
import           ZkFold.Symbolic.Types                          (Symbolic)

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash :: forall a . Symbolic a => Natural -> a -> a -> a -> a
mimcHash nRounds k xL xR =
    let c  = mimcConstants !! (nRounds-!1)
        t5 = (xL + k + c) ^ (5 :: Natural)
    in bool (xR + t5) (mimcHash (nRounds-!1) k (xR + t5) xL) (nRounds > 1)
