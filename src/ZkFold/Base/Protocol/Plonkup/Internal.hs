{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Internal where

import           GHC.Generics                                        (Par1)
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

data Plonk (i :: Natural) (n :: Natural) (l :: Natural) curve1 curve2 transcript = Plonk {
        omega :: ScalarField curve1,
        k1    :: ScalarField curve1,
        k2    :: ScalarField curve1,
        iPub  :: Vector l (Var (Vector i)),
        ac    :: ArithmeticCircuit (ScalarField curve1) (Vector i) Par1,
        x     :: ScalarField curve1
    }

type PlonkPermutationSize n = 3 * n

-- The maximum degree of the polynomials we need in the protocol is `4 * n + 5`.
type PlonkPolyExtendedLength n = 4 * n + 6

type PlonkPolyExtended n c = PolyVec (ScalarField c) (PlonkPolyExtendedLength n)

instance (Show (ScalarField c1), Arithmetic (ScalarField c1), KnownNat l, KnownNat i) => Show (Plonk i n l c1 c2 t) where
    show (Plonk omega k1 k2 iPub ac x) =
        "Plonk: " ++ show omega ++ " " ++ show k1 ++ " " ++ show k2 ++ " " ++ show iPub ++ " " ++ show ac ++ " " ++ show x

instance (KnownNat i, KnownNat n, KnownNat l, Arithmetic (ScalarField c1), Arbitrary (ScalarField c1)) => Arbitrary (Plonk i n l c1 c2 t) where
    arbitrary = do
        ac <- arbitrary
        vecPubInp <- genSubset (getAllVars ac) (value @l)
        let (omega, k1, k2) = getParams (value @n)
        Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
