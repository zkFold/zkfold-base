{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Data.Functor.Constant                   (Constant (..))
import           Data.Zip                                (Zip (..))
import           Prelude                                 hiding (Num (..), sum, take, zipWith)
import           System.Random                           (Random (..), mkStdGen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.Vector                 (Vector, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Prelude                          (take)

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

instance
  ( CyclicGroup (Weierstrass curve (Point field))
  , Random (ScalarFieldOf (Weierstrass curve (Point field)))
  ) => PedersonSetup [] (Weierstrass curve (Point field)) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: ScalarFieldOf (Weierstrass curve (Point field))
        in take (value @PedersonSetupMaxSize) $ iterate (scale x) pointGen

instance
  ( KnownNat n
  , CyclicGroup (Weierstrass curve (Point field))
  , Random (ScalarFieldOf (Weierstrass curve (Point field)))
  , n <= PedersonSetupMaxSize
  ) => PedersonSetup (Vector n) (Weierstrass curve (Point field)) where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        unsafeToVector $ take (value @n) $ groupElements @[]

instance (PedersonSetup s g, Functor s) => PedersonSetup s (Constant g a) where
    groupElements = Constant <$> groupElements @s

instance
  ( PedersonSetup s g
  , Zip s
  , Foldable s
  , Scale f g
  , AdditiveGroup g
  ) => HomomorphicCommit (s f) g where
    hcommit v = sum $ zipWith scale v groupElements
