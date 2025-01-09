{-# LANGUAGE AllowAmbiguousTypes  #-}

module ZkFold.Base.Protocol.IVC.Oracle where

import           Data.Foldable                                  (Foldable (..))
import           Prelude                                        ((.), (++), concatMap)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHashN)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)

class HashAlgorithm algo where
    hash :: forall x . Ring x => [x] -> x

data MiMCHash
instance HashAlgorithm MiMCHash where
    hash :: forall a . Ring a => [a] -> a
    hash = mimcHashN @a mimcConstants zero

oracle :: forall algo x a . (HashAlgorithm algo, RingRepresentation x a) => x -> a
oracle = hash @algo . toList . rrep

class Ring a => RingRepresentation x a where
    rrep :: x -> [a]

instance {-# INCOHERENT #-} Ring a => RingRepresentation a a where
    rrep a = [a]

instance {-# INCOHERENT #-} (RingRepresentation b a, RingRepresentation c a) => RingRepresentation (b, c) a where
    rrep (b, c) = rrep b ++ rrep c

instance {-# INCOHERENT #-} (RingRepresentation b a, RingRepresentation c a, RingRepresentation d a) => RingRepresentation (b, c, d) a where
    rrep (b, c, d) = rrep b ++ rrep c ++ rrep d

instance {-# INCOHERENT #-} (RingRepresentation b a, RingRepresentation c a, RingRepresentation d a, RingRepresentation e a) => RingRepresentation (b, c, d, e) a where
    rrep (b, c, d, e) = rrep b ++ rrep c ++ rrep d ++ rrep e

instance {-# INCOHERENT #-} (RingRepresentation b a) => RingRepresentation (Vector n b) a where
    rrep = concatMap rrep . toList

instance (Ring a, Foldable f) => RingRepresentation (f a) a where
    rrep = toList
