module ZkFold.Symbolic.Algorithms.Hash.MiMC (mimcHash, hash) where

import           Data.Foldable                   (Foldable (..))
import           Data.Functor.Identity           (Identity (..))
import           Data.List.NonEmpty              (NonEmpty ((:|)), nonEmpty)
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Eq (..), Num (..), any, length, not, (!!), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash :: Semiring a => [a] -> a -> a -> a -> a
mimcHash xs k = case nonEmpty (reverse xs) of
    Just cs -> go cs
    Nothing -> error "mimcHash: empty list"
    where
        go (c :| cs) xL xR =
          let t5 = (xL + k + c) ^ (5 :: Natural)
           in case nonEmpty cs of
              Just cs' -> go cs' (xR + t5) xL
              Nothing  -> xR + t5

hash :: (Semiring a, Foldable u) => u a -> Identity a
hash datum = Identity $ case toList datum of
    []         -> zero
    [x]        -> mimcHash mimcConstants zero zero x
    [xL, xR]   -> mimcHash mimcConstants zero xL xR
    (xL:xR:xZ) -> mimcHash (zero : xZ ++ [zero]) zero xL xR
