{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Control.DeepSeq                             (NFData)
import           Data.Void                                   (Void)
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
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Prelude                              (take)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Data.Ed25519                ()
import           ZkFold.Symbolic.Data.FFA                    (Size)

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
        in fromList $ take (value @n) $ iterate (scale x) gen

instance (KnownNat n, Symbolic c, NFData (c (Vector Size)))
        => PedersonSetup n (Point (Ed25519 c)) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: ScalarField (Ed25519 Void)
        in fromList $ take (value @n) $ iterate (scale x) gen

instance (PedersonSetup n c, Scale f c, AdditiveGroup c) => HomomorphicCommit (Vector n f) c where
    hcommit v = sum $ zipWith scale v groupElements

instance (PedersonSetup 100 c, Scale f c, AdditiveGroup c) => HomomorphicCommit [f] c where
    hcommit v = sum $ zipWith scale v (toList $ groupElements @100)
