{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE NoOverloadedStrings  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.Oracle where

import           Data.Char                                      (ord)
import           Data.Proxy                                     (Proxy (..))
import qualified Data.Vector                                    as V
import           GHC.Generics
import           GHC.TypeLits
import           Prelude                                        (foldl, ($), (.), (<$>))
import qualified Prelude                                        as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHash2)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)

class RandomOracle a b where
    oracle :: a -> b
    default oracle :: (Generic a, RandomOracle' (Rep a) b) => a -> b
    oracle = oracle' . from

instance (Ring a, FromConstant P.Integer a) => RandomOracle P.Integer a where
    oracle = oracle @a . fromConstant

instance Ring a => RandomOracle a a where
    oracle a = mimcHash2 mimcConstants a zero zero

instance (Ring b, RandomOracle a b) => RandomOracle [a] b where
    oracle = foldl (\acc x -> let y = oracle x in y * acc + y) zero

instance (Ring b, RandomOracle a b) => RandomOracle (V.Vector a) b where
    oracle = foldl (\acc x -> let y = oracle x in y * acc + y) zero

instance {-# OVERLAPPABLE #-} (Generic a, RandomOracle' (Rep a) b) => RandomOracle a b where

class RandomOracle' f b where
    oracle' :: f a -> b

instance (RandomOracle' f b, RandomOracle' g b) => RandomOracle' (f :+: g) b where
    oracle' (L1 x) = oracle' x
    oracle' (R1 x) = oracle' x

-- TODO: it is not secure if we know the preimage of 0 or (-1).
instance (RandomOracle' f b, RandomOracle' g b, Ring b) => RandomOracle' (f :*: g) b where
    oracle' (x :*: y) =
        let z1 = oracle' x
            z2 = oracle' y
        in z1 * z2 + z1

instance RandomOracle c b => RandomOracle' (K1 i c) b where
    oracle' (K1 x) = oracle x

-- | Handling constructors with no fields.
-- The oracle will be based on the constructor's name
--
instance {-# OVERLAPPING #-}
    ( KnownSymbol conName
    , Ring a
    , FromConstant Natural a
    ) => RandomOracle' (M1 C ('MetaCons conName fixity selectors) U1) a where
    oracle' _ = oracle @[a] $ (fromConstant @Natural . P.fromIntegral . ord) <$> symbolVal (Proxy @conName)

instance RandomOracle' f b => RandomOracle' (M1 c m f) b where
    oracle' (M1 x) = oracle' x
