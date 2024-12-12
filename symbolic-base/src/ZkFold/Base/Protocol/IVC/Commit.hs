{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Data.Functor.Constant                       (Constant (..))
import           Data.Zip                                    (Zip (..))
import           Prelude                                     hiding (Num (..), sum, take, zipWith)
import           System.Random                               (Random (..), mkStdGen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.Vector                     (Vector, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Prelude                              (take)

-- | Commit to the object @a@ with commitment key @ck@ and results of type @f@
--
class Commit algo a f where
    commit :: a -> f

instance RandomOracle algo a x => Commit algo a x where
    commit = oracle @algo

-- | Homomorphic commitment scheme, i.e. (hcommit x) * (hcommit y) == hcommit (x + y)
--
class AdditiveGroup c => HomomorphicCommit a c where
    hcommit :: a -> c

class PedersonSetup s c where
    groupElements :: s c

type PedersonSetupMaxSize = 100

instance (EllipticCurve curve, Random (ScalarField curve)) => PedersonSetup [] (Point curve) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: ScalarField curve
        in take (value @PedersonSetupMaxSize) $ iterate (mul x) gen

instance (KnownNat n, EllipticCurve curve, Random (ScalarField curve), n <= PedersonSetupMaxSize) => PedersonSetup (Vector n) (Point curve) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        unsafeToVector $ take (value @n) $ groupElements @[]

instance (PedersonSetup s (Point curve), Functor s) => PedersonSetup s (Constant (Point curve) a) where
    groupElements = Constant <$> groupElements @s

instance (PedersonSetup s c, Zip s, Foldable s, Scale f c, AdditiveGroup c) => HomomorphicCommit (s f) c where
    hcommit v = sum $ zipWith scale v groupElements
