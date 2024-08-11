{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.Oracle where

import           GHC.Generics
import           Prelude                                        (($), (.), (<$>))
import qualified Prelude                                        as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHash2)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)

class RandomOracle a b where
    oracle :: a -> b
    default oracle :: (Generic a, RandomOracle' (Rep a) b) => a -> b
    oracle = oracle' . from

instance {-# OVERLAPPING #-} Ring a => RandomOracle a a where
    oracle a = mimcHash2 mimcConstants a zero zero

instance {-# OVERLAPPING #-} (AdditiveMonoid b, RandomOracle a b) => RandomOracle [a] b where
    oracle as = sum $ oracle <$> as

instance (Generic a, RandomOracle' (Rep a) b) => RandomOracle a b where

class RandomOracle' f b where
    oracle' :: f a -> b

instance RandomOracle' V1 b where
    oracle' = P.undefined

instance RandomOracle' U1 b where
    oracle' = P.undefined

instance (RandomOracle' f b, RandomOracle' g b) => RandomOracle' (f :+: g) b where
    oracle' (L1 x) = oracle' x
    oracle' (R1 x) = oracle' x

instance (RandomOracle' f b, RandomOracle' g b, AdditiveSemigroup b) => RandomOracle' (f :*: g) b where
    oracle' (x :*: y) = oracle' x + oracle' y

instance RandomOracle c b => RandomOracle' (K1 i c) b where
    oracle' (K1 x) = oracle x

instance (RandomOracle' f) b => RandomOracle' (M1 c m f) b where
    oracle' (M1 x) = oracle' x
