{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.IVC.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Data.Functor.Constant                       (Constant (..))
import           Data.Zip                                    (Zip (..))
import           GHC.Generics                                (Par1 (..))
import           Prelude                                     hiding (Num (..), sum, take, zipWith, (^))
import           System.Random                               (Random (..), mkStdGen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.Vector                     (Vector, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Prelude                              (take)

-- | Commit to the object @x@ with commitment of type @a@ using the algorithm @algo@
--
class Commit algo x a where
    commit :: x -> a

instance (HashAlgorithm algo, RingRepresentation x a) => Commit algo x a where
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
        in take (value @PedersonSetupMaxSize) $ iterate (mul x) pointGen

instance (KnownNat n, EllipticCurve curve, Random (ScalarField curve), n <= PedersonSetupMaxSize) => PedersonSetup (Vector n) (Point curve) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        unsafeToVector $ take (value @n) $ groupElements @[]

instance (PedersonSetup s (Point curve), Functor s) => PedersonSetup s (Constant (Point curve) a) where
    groupElements = Constant <$> groupElements @s

instance (PedersonSetup s c, Zip s, Foldable s, Scale f c, AdditiveGroup c) => HomomorphicCommit (s f) c where
    hcommit v = sum $ zipWith scale v groupElements

--------------------------------------------------------------------------------

-- For testing purposes

instance (FiniteField f) => AdditiveSemigroup (Par1 f) where
    Par1 x + Par1 y = Par1 $ x + y

instance (FiniteField f) => Scale Natural (Par1 f) where
    scale x (Par1 y) = Par1 $ natScale x y

instance (FiniteField f) => AdditiveMonoid (Par1 f) where
    zero = Par1 zero

instance (FiniteField f) => Scale Integer (Par1 f) where
    scale x (Par1 y) = Par1 $ intScale x y

instance (FiniteField f) => AdditiveGroup (Par1 f) where
    negate (Par1 x) = Par1 $ negate x

instance {-# INCOHERENT #-} (FiniteField f) => Scale f (Par1 f) where
    scale x y = Par1 $ x * unPar1 y

instance (FiniteField f) => PedersonSetup [] (Par1 f) where
    groupElements =
        let x = toConstant $ fst $ random @(Zp BLS12_381_Scalar) $ mkStdGen 0 
        in take (value @PedersonSetupMaxSize) $ map Par1 $ iterate (natScale x) (one + one)