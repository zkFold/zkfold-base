{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE NoOverloadedStrings  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.Oracle where

import           Data.Char                                           (ord)
import           Data.Map.Strict                                     (Map)
import qualified Data.Map.Strict                                     as M
import           Data.Proxy                                          (Proxy (..))
import           GHC.Generics
import           GHC.TypeLits
import           Prelude                                             (($), (.), (<$>))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC                (mimcHash2)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants      (mimcConstants)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

class RandomOracle a b where
    oracle :: a -> b
    default oracle :: (Generic a, RandomOracle' (Rep a) b) => a -> b
    oracle = oracle' . from

instance (AdditiveMonoid b, RandomOracle a b) => RandomOracle (Map k a) b where
    oracle = oracle . M.elems

instance (Ring a, FromConstant Natural a) => RandomOracle (ArithmeticCircuit a (Vector n)) a where
    oracle ArithmeticCircuit{..} = oracle (acRange, fromConstant @_ @a <$> acInput, fromConstant @_ @a <$> acVarOrder, fromConstant @_ @a <$> acOutput)

instance Ring a => RandomOracle a a where
    oracle a = mimcHash2 mimcConstants a zero zero

instance (AdditiveMonoid b, RandomOracle a b) => RandomOracle [a] b where
    oracle as = sum $ oracle <$> as

instance {-# OVERLAPPABLE #-} (Generic a, RandomOracle' (Rep a) b) => RandomOracle a b where

class RandomOracle' f b where
    oracle' :: f a -> b

instance RandomOracle' V1 b where
    oracle' = P.undefined -- No oracle for uninhabited types

instance RandomOracle' U1 b where
    oracle' = P.undefined -- No useful information can be extracted from U1.
                          -- Oracle is calculated based on the constructor name instead in
                          -- instance RandomOracle' (M1 C ('MetaCons conName fixity selectors) U1) b

instance (RandomOracle' f b, RandomOracle' g b) => RandomOracle' (f :+: g) b where
    oracle' (L1 x) = oracle' x
    oracle' (R1 x) = oracle' x

instance (RandomOracle' f b, RandomOracle' g b, AdditiveSemigroup b) => RandomOracle' (f :*: g) b where
    oracle' (x :*: y) = oracle' x + oracle' y

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
