{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Internal where

import           Data.Binary                                         (Binary)
import           Data.Constraint                                     (withDict)
import           Data.Constraint.Nat                                 (plusNat, timesNat)
import           Data.Functor.Rep                                    (Rep)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Algebra.Polynomials.Univariate          (PolyVec)
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Base.Protocol.Plonkup.Utils
import           ZkFold.Symbolic.Compiler                            ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

{-
    NOTE: we need to parametrize the type of transcripts because we use BuiltinByteString on-chain and ByteString off-chain.
    Additionally, we don't want this library to depend on Cardano libraries.
-}

data Plonkup (i :: Natural) p (n :: Natural) (l :: Natural) curve1 curve2 transcript = Plonkup {
        omega :: ScalarField curve1,
        k1    :: ScalarField curve1,
        k2    :: ScalarField curve1,
        ac    :: ArithmeticCircuit (ScalarField curve1) p (Vector i) (Vector l),
        x     :: ScalarField curve1
    }

type PlonkupPermutationSize n = 3 * n

-- The maximum degree of the polynomials we need in the protocol is `4 * n + 5`.
type PlonkupPolyExtendedLength n = 4 * n + 6


with4n6 :: forall n {r}. KnownNat n => (KnownNat (4 * n + 6) => r) -> r
with4n6 f = withDict (timesNat @4 @n) (withDict (plusNat @(4 * n) @6) f)

type PlonkupPolyExtended n c = PolyVec (ScalarField c) (PlonkupPolyExtendedLength n)

instance (Show (ScalarField c1), Arithmetic (ScalarField c1), KnownNat l, KnownNat i) => Show (Plonkup i p n l c1 c2 t) where
    show Plonkup {..} =
        "Plonkup: " ++ show omega ++ " " ++ show k1 ++ " " ++ show k2 ++ " " ++ show (acOutput ac)  ++ " " ++ show ac ++ " " ++ show x

instance
  ( KnownNat i, KnownNat n, KnownNat l
  , Arithmetic (ScalarField c1), Arbitrary (ScalarField c1), Binary (ScalarField c1)
  , Binary (Rep p)
  ) => Arbitrary (Plonkup i p n l c1 c2 t) where
    arbitrary = do
        ac <- arbitrary
        let (omega, k1, k2) = getParams (value @n)
        Plonkup omega k1 k2 ac <$> arbitrary
