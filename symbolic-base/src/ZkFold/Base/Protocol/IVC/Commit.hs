{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.IVC.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Control.DeepSeq                             (NFData (..))
import           Data.Binary                                 (Binary (..), decode, encode)
import           Data.Functor.Rep                            (Representable (..), WrappedRep (..))
import           Data.Zip                                    (Zip (..))
import           GHC.Generics                                (Par1 (..))
import           Prelude                                     hiding (Bool (..), Eq (..), Num (..), sum, take, zipWith,
                                                              (^))
import qualified Prelude                                     as Haskell
import           System.Random                               (Random (..), mkStdGen)
import           Test.QuickCheck                             (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (CyclicGroup (..))
import           ZkFold.Base.Data.ByteString                 (LittleEndian (..))
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.Conditional            (Conditional (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

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

instance {-# OVERLAPPING #-}
    ( CyclicGroup g
    , Random (ScalarFieldOf g)
    ) => PedersonSetup [] g where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: ScalarFieldOf g
        in iterate (scale x) pointGen

instance
    ( CyclicGroup g
    , Random (ScalarFieldOf g)
    , Representable s
    , Binary (Rep s)
    , Exponent (ScalarFieldOf g) Natural
    ) => PedersonSetup s g where
    groupElements =
        -- TODO: This is just for testing purposes! Not to be used in production
        let x = fst $ random $ mkStdGen 0 :: ScalarFieldOf g
            f = unLittleEndian . decode . encode
        in tabulate (\i -> scale (x^f i) pointGen)

instance
  ( PedersonSetup s g
  , Zip s
  , Foldable s
  , Scale f g
  , AdditiveGroup g
  ) => HomomorphicCommit (s f) g where
    hcommit v = sum $ zipWith scale v groupElements

--------------------------------------------------------------------------------

-- Par1 is currently used as a placeholder for the foreign field element and elliptic curve point types
-- TODO: remove once we finish FFA and EC refactors

instance {-# INCOHERENT #-} NFData (WrappedRep Par1) where
    rnf (WrapRep ()) = rnf ()

instance {-# INCOHERENT #-} Binary (WrappedRep Par1) where
    put (WrapRep ()) = pure ()
    get = pure $ WrapRep ()

instance {-# INCOHERENT #-} Haskell.Eq (WrappedRep Par1) where
    _ == _ = Haskell.True

instance {-# INCOHERENT #-} Haskell.Eq (WrappedRep Par1) => Ord (WrappedRep Par1) where
    compare _ _ = EQ

instance Finite f => Finite (Par1 f) where
    type Order (Par1 f) = Order f

instance FromConstant Natural f => FromConstant Natural (Par1 f) where
    fromConstant x = Par1 $ fromConstant x

instance FromConstant Integer f => FromConstant Integer (Par1 f) where
    fromConstant x = Par1 $ fromConstant x

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

instance (FiniteField f) => MultiplicativeSemigroup (Par1 f) where
    Par1 x * Par1 y = Par1 $ x * y

instance Exponent f Natural => Exponent (Par1 f) Natural where
    (^) (Par1 x) n = Par1 $ x ^ n

instance (FiniteField f) => MultiplicativeMonoid (Par1 f) where
    one = Par1 one

instance (FiniteField f) => Semiring (Par1 f)

instance (FiniteField f) => Ring (Par1 f)

instance Exponent f Integer => Exponent (Par1 f) Integer where
    (^) (Par1 x) n = Par1 $ x ^ n

instance (FiniteField f) => Field (Par1 f) where
    (//) (Par1 x) (Par1 y) = Par1 $ x // y

-- instance (FiniteField f) => CyclicGroup (Par1 f) where
--     type ScalarFieldOf (Par1 f) = f
--     pointGen = Par1 (one + one)

instance Symbolic ctx => Conditional (Bool ctx) (Par1 (FieldElement ctx)) where
    bool x y b = Par1 $ bool (unPar1 x) (unPar1 y) b

instance Symbolic ctx => Eq (Bool ctx) (Par1 (FieldElement ctx)) where
    Par1 x == Par1 y = x == y

instance {-# OVERLAPPING #-} (FiniteField f) => PedersonSetup [] (Par1 f) where
    groupElements =
        let x = toConstant $ fst $ random @(Zp BLS12_381_Scalar) $ mkStdGen 0
        in map Par1 $ iterate (natScale x) (one + one)

instance Arbitrary f => Arbitrary (Par1 f) where
    arbitrary = Par1 <$> arbitrary
