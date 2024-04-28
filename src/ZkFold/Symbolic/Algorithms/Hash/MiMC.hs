module ZkFold.Symbolic.Algorithms.Hash.MiMC (mimcHash) where

import           Data.List.NonEmpty              (NonEmpty ((:|)), nonEmpty)
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Eq (..), Num (..), any, length, not, (!!), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Types           (Symbolic)

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash :: forall a . Symbolic a => [a] -> a -> a -> a -> a
mimcHash xs k = case nonEmpty (reverse xs) of
    Just cs -> go cs
    Nothing -> error "mimcHash: empty list"
    where
        go (c :| cs) xL xR =
          let t5 = (xL + k + c) ^ (5 :: Natural)
           in case nonEmpty cs of
              Just cs' -> go cs' (xR + t5) xL
              Nothing  -> xR + t5
