{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Data.Zip                                    (zipWith)
import           GHC.IsList                                  (IsList (..))
import           Prelude                                     hiding (Num (..), sum, take, zipWith)
import           System.Random                               (Random (..), mkStdGen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Prelude                              (take)

-- | Commit to the object @a@ with commitment key @ck@ and results of type @f@
--
class Commit a f where
    commit :: a -> f

instance RandomOracle a x => Commit a x where
    commit = oracle

-- | Homomorphic commitment scheme, i.e. (hcommit x) * (hcommit y) == hcommit (x + y)
--
class AdditiveGroup c => HomomorphicCommit a c where
    hcommit :: a -> c

class PedersonSetup n c where
    groupElements :: Vector n c

instance KnownNat n => PedersonSetup n (Point BLS12_381_G1) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: Zp BLS12_381_Scalar
        in fromList $ take (value @n) $ iterate (scale x) pointGen

instance KnownNat n => PedersonSetup n (Point Ed25519) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: ScalarField Ed25519
        in fromList $ take (value @n) $ iterate (scale x) pointGen

instance (PedersonSetup n c, Scale f c, AdditiveGroup c) => HomomorphicCommit (Vector n f) c where
    hcommit v = sum $ zipWith scale v groupElements

instance (PedersonSetup 100 c, Scale f c, AdditiveGroup c) => HomomorphicCommit [f] c where
    hcommit v = sum $ zipWith scale v (toList $ groupElements @100)
