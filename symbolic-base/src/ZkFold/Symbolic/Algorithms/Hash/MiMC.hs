{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Algorithms.Hash.MiMC where

import           Data.Foldable                                  (toList)
import           Data.List.NonEmpty                             (NonEmpty ((:|)), nonEmpty)
import           Data.Proxy                                     (Proxy (..))
import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Eq (..), Num (..), any, length, not, (!!), (/),
                                                                 (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.HFunctor                      (hmap)
import           ZkFold.Base.Data.Package                       (unpacked)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.FieldElement

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash2 :: (FromConstant a x, Ring x) => [a] -> a -> x -> x -> x
mimcHash2 (map fromConstant -> xs) (fromConstant -> k) = case nonEmpty (reverse xs) of
    Just cs -> go cs
    Nothing -> error "mimcHash: empty list"
    where
        go (c :| cs) xL xR =
          let t5 = (xL + k + c) ^ (5 :: Natural)
           in case nonEmpty cs of
              Just cs' -> go cs' (xR + t5) xL
              Nothing  -> xR + t5

mimcHashN :: (FromConstant a x, Ring x) => [a] -> a -> [x] -> x
mimcHashN xs k = go
  where
    go zs = case zs of
      []          -> mimcHash2 xs k zero zero
      [z]         -> mimcHash2 xs k zero z
      [zL, zR]    -> mimcHash2 xs k zL zR
      (zL:zR:zs') -> go (mimcHash2 xs k zL zR : zs')

hash :: forall context x a .
    ( SymbolicOutput x
    , BaseField context ~ a
    , Context x ~ context
    ) => x -> FieldElement context
hash = mimcHashN mimcConstants (zero :: a) . fmap FieldElement . unpacked . hmap toList . flip arithmetize Proxy
