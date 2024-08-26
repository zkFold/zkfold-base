{-# LANGUAGE DeriveAnyClass #-}

module ZkFold.Base.Protocol.ARK.Protostar.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Control.DeepSeq                           (NFData)
import           GHC.Generics                              (Generic)
import           Prelude                                   (zipWith, ($), (<$>))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Protocol.ARK.Protostar.Oracle

-- | Commit to the object @a@ with commitment key @ck@ and results of type @f@
--
class Commit ck a f where
    commit :: ck -> a -> f

instance (RandomOracle ck x, RandomOracle a x, Ring x) => Commit ck a x where
    commit ck a = oracle [oracle @ck @x ck, oracle @a @x a]

-- | Homomorphic commitment scheme, i.e. (hcommit ck1 a1) * (hcommit ck2 a2) == hcommit (ck1 + ck2) (a1 + a2)
--
class HomomorphicCommit ck a f where
    hcommit :: ck -> a -> f

class PedersonSetup a where
    pedersonGH :: (a, a)

instance PedersonSetup (Zp BLS12_381_Scalar) where
    pedersonGH = (g, h)
        where
            -- Random elements of Zp BLS12_381_Scalar
            -- TODO: Consider choosing these elements randomly each time instead of hardcoding them
            g = toZp 40136933577475258330825008995712625700732059996343366400386587459390107738728
            h = toZp 33848815739574706259584769715284676658282333449257982457879775984963591668910

-- | Pedersen commitment scheme
-- Commitment key consists of field elements g and h, and randomness r
--
instance {-# OVERLAPPABLE #-} (Exponent a b, Exponent a a, PedersonSetup a) => HomomorphicCommit a b a where
    hcommit r b = let (g, h) = pedersonGH @a
                   in g^b * h^r

-- Pedersen commitment scheme for lists extending the homomorphism to elementwise sums:
-- (hcommit ck l1) * (hcommit ck l2) = hcommit ck (zipWith (+) l1 l2)
-- This is required for AccumulatorScheme
--
instance (MultiplicativeMonoid a, Exponent a Natural, HomomorphicCommit a b a) => HomomorphicCommit a [b] a where
    hcommit ck lst = product $ zipWith (^) (hcommit ck <$> lst) [1 :: Natural ..]
