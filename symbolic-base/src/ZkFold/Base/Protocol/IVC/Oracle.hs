{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.Oracle where

import qualified Data.Vector                                    as V
import           GHC.Generics
import           Prelude                                        ((.), map)
import qualified Prelude                                        as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHashN)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)

class HashAlgorithm algo a where
    hash :: [a] -> a

data MiMCHash
instance Ring a => HashAlgorithm MiMCHash a where
    hash = mimcHashN @a mimcConstants zero

class RandomOracle algo a b where
    oracle :: a -> b
    default oracle :: (Generic a, RandomOracle' algo (Rep a) b) => a -> b
    oracle = oracle' @algo . from

instance (FromConstant P.Integer a, HashAlgorithm algo a) => RandomOracle algo P.Integer a where
    oracle = oracle @algo @a . fromConstant

instance HashAlgorithm algo a => RandomOracle algo a a where
    oracle a = hash @algo [a]

instance HashAlgorithm algo a => RandomOracle algo (a, a) a where
    oracle (a, b) = hash @algo [a, b]

instance {-# OVERLAPPING #-} HashAlgorithm algo a => RandomOracle algo [a] a where
    oracle = hash @algo

instance (HashAlgorithm algo b, RandomOracle algo a b) => RandomOracle algo [a] b where
    oracle = hash @algo . map (oracle @algo)

instance (HashAlgorithm algo b, RandomOracle algo a b) => RandomOracle algo (V.Vector a) b where
    oracle = (oracle @algo) . V.toList

instance {-# OVERLAPPABLE #-} (Generic a, RandomOracle' algo (Rep a) b) => RandomOracle algo a b where

class RandomOracle' algo f b where
    oracle' :: f a -> b

instance (RandomOracle' algo f b, RandomOracle' algo g b, HashAlgorithm algo b, Ring b) => RandomOracle' algo (f :+: g) b where
    oracle' (L1 x) = oracle' @algo x
    oracle' (R1 x) = oracle @algo (zero :: b, oracle' @algo x :: b)

instance (RandomOracle' algo f b, RandomOracle' algo g b, HashAlgorithm algo b) => RandomOracle' algo (f :*: g) b where
    oracle' (x :*: y) =
        let z1 = oracle' @algo x :: b
            z2 = oracle' @algo y :: b
        in oracle @algo (z1, z2)

instance RandomOracle algo c b => RandomOracle' algo (K1 i c) b where
    oracle' (K1 x) = oracle @algo x

-- | Handling constructors with no fields.
instance {-# OVERLAPPING #-}
    Ring a => RandomOracle' algo (M1 C ('MetaCons conName fixity selectors) U1) a where
    oracle' _ = zero

instance RandomOracle' algo f b => RandomOracle' algo (M1 c m f) b where
    oracle' (M1 x) = oracle' @algo x
