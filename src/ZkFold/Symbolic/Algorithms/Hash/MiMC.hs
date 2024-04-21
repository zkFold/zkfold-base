module ZkFold.Symbolic.Algorithms.Hash.MiMC (mimcHash) where

import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Eq (..), Num (..), any, not, (!!), (/), (^),
                                                                 (||), length)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                 (length)
import           ZkFold.Symbolic.Data.Conditional               (bool)
import           ZkFold.Symbolic.Types                          (Symbolic)

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash :: forall a . Symbolic a => [a] -> a -> a -> a -> a
mimcHash cs k xL xR =
    let c  = last cs
        t5 = (xL + k + c) ^ (5 :: Natural)
    in bool (xR + t5) (mimcHash (init cs) k (xR + t5) xL) (length cs > 1)
