{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Utils where

import           Data.Bifunctor                                      (first)
import           Data.Bool                                           (bool)
import           Data.Map.Strict                                     (Map)
import           GHC.Generics                                        (Generic)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           System.Random                                       (RandomGen, mkStdGen, uniformR)
import           Test.QuickCheck                                     (Arbitrary (..), Gen, shuffle)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector(..), unsafeToVector)
import           ZkFold.Prelude                                      (log2ceiling, take)
import           ZkFold.Symbolic.Compiler                            ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

getParams :: forall a . (Eq a, FiniteField a) => Natural -> (a, a, a)
getParams n = findK' $ mkStdGen 0
    where
        omega = case rootOfUnity @a (log2ceiling n) of
                  Just o -> o
                  _      -> error "impossible"
        hGroup = map (omega^) [0 .. n-!1]
        hGroup' k = map (k*) hGroup

        findK' :: RandomGen g => g -> (a, a, a)
        findK' g =
            let (k1, g') = first fromConstant $ uniformR (1, order @a -! 1) g
                (k2, g'') = first fromConstant $ uniformR (1, order @a -! 1) g'
            in bool (findK' g'') (omega, k1, k2) $
                all (`notElem` hGroup) (hGroup' k1)
                && all (`notElem` hGroup' k1) (hGroup' k2)

genSubset :: [Var (Vector i)] -> Natural -> Gen [Var (Vector i)]
genSubset vars maxLength = take maxLength <$> shuffle vars

type PlonkPermutationSize n = 3 * n

-- The maximum degree of the polynomials we need in the protocol is `4 * n + 5`.
type PlonkPolyExtendedLength n = 4 * n + 6

type PlonkPolyExtended n c = PolyVec (ScalarField c) (PlonkPolyExtendedLength n)

data PlonkPermutation n c = PlonkPermutation {
        s1 :: PolyVec (ScalarField c) n,
        s2 :: PolyVec (ScalarField c) n,
        s3 :: PolyVec (ScalarField c) n
    }
instance Show (ScalarField c) => Show (PlonkPermutation n c) where
    show (PlonkPermutation s1 s2 s3) = "Permutation: " ++ show s1 ++ " " ++ show s2 ++ " " ++ show s3

data PlonkCircuitPolynomials n c = PlonkCircuitPolynomials {
        ql     :: PlonkPolyExtended n c,
        qr     :: PlonkPolyExtended n c,
        qo     :: PlonkPolyExtended n c,
        qm     :: PlonkPolyExtended n c,
        qc     :: PlonkPolyExtended n c,
        qk     :: PlonkPolyExtended n c,
        sigma1 :: PlonkPolyExtended n c,
        sigma2 :: PlonkPolyExtended n c,
        sigma3 :: PlonkPolyExtended n c
    }
instance Show (ScalarField c) => Show (PlonkCircuitPolynomials n c) where
    show (PlonkCircuitPolynomials ql qr qo qm qc qk sigma1 sigma2 sigma3) =
        "Circuit Polynomials: "
        ++ show ql ++ " "
        ++ show qr ++ " "
        ++ show qo ++ " "
        ++ show qm ++ " "
        ++ show qc ++ " "
        ++ show qk ++ " "
        ++ show sigma1 ++ " "
        ++ show sigma2 ++ " "
        ++ show sigma3

data PlonkCircuitCommitments c = PlonkCircuitCommitments {
        cmQl :: Point c,
        cmQr :: Point c,
        cmQo :: Point c,
        cmQm :: Point c,
        cmQc :: Point c,
        cmQk :: Point c,
        cmS1 :: Point c,
        cmS2 :: Point c,
        cmS3 :: Point c
    }
instance (Show (BaseField c), EllipticCurve c) => Show (PlonkCircuitCommitments c) where
    show (PlonkCircuitCommitments cmQl cmQr cmQo cmQm cmQc cmQk cmS1 cmS2 cmS3) =
        "Circuit Commitments: "
        ++ show cmQl ++ " "
        ++ show cmQr ++ " "
        ++ show cmQo ++ " "
        ++ show cmQm ++ " "
        ++ show cmQc ++ " "
        ++ show cmQk ++ " "
        ++ show cmS1 ++ " "
        ++ show cmS2 ++ " "
        ++ show cmS3

newtype PlonkWitnessMap n i c = PlonkWitnessMap
    (PlonkWitnessInput i c -> (PolyVec (ScalarField c) n, PolyVec (ScalarField c) n, PolyVec (ScalarField c) n))

data PlonkWitnessInput i c = PlonkWitnessInput (Vector i (ScalarField c)) (Map Natural (ScalarField c))
instance Show (ScalarField c) => Show (PlonkWitnessInput i c) where
    show (PlonkWitnessInput v m) = "Witness Input: " ++ show v <> "Witness New Vars: " ++ show m

data PlonkProverSecret c = PlonkProverSecret {
        b1  :: ScalarField c,
        b2  :: ScalarField c,
        b3  :: ScalarField c,
        b4  :: ScalarField c,
        b5  :: ScalarField c,
        b6  :: ScalarField c,
        b7  :: ScalarField c,
        b8  :: ScalarField c,
        b9  :: ScalarField c,
        b10 :: ScalarField c,
        b11 :: ScalarField c,
        b12 :: ScalarField c,
        b13 :: ScalarField c,
        b14 :: ScalarField c,
        b15 :: ScalarField c,
        b16 :: ScalarField c,
        b17 :: ScalarField c,
        b18 :: ScalarField c,
        b19 :: ScalarField c
    } deriving Generic

instance Show (ScalarField c) => Show (PlonkProverSecret c) where
    show (PlonkProverSecret b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19) =
        "Prover Secret: "
        ++ show b1 ++ " "
        ++ show b2 ++ " "
        ++ show b3 ++ " "
        ++ show b4 ++ " "
        ++ show b5 ++ " "
        ++ show b6 ++ " "
        ++ show b7 ++ " "
        ++ show b8 ++ " "
        ++ show b9 ++ " "
        ++ show b10 ++ " "
        ++ show b11 ++ " "
        ++ show b12 ++ " "
        ++ show b13 ++ " "
        ++ show b14 ++ " "
        ++ show b15 ++ " "
        ++ show b16 ++ " "
        ++ show b17 ++ " "
        ++ show b18 ++ " "
        ++ show b19

instance Arbitrary (ScalarField c) => Arbitrary (PlonkProverSecret c) where
    arbitrary = PlonkProverSecret <$>
        arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary

newtype PlonkInput l c = PlonkInput { unPlonkInput :: Vector l (ScalarField c) }
instance Show (ScalarField c) => Show (PlonkInput l c) where
    show (PlonkInput v) = "Input: " ++ show v

instance (KnownNat l, Arbitrary (ScalarField c)) => Arbitrary (PlonkInput l c) where
    arbitrary = do
        PlonkInput . unsafeToVector . take (value @l) <$> arbitrary

data PlonkProof c = PlonkProof {
        cmA       :: Point c,
        cmB       :: Point c,
        cmC       :: Point c,
        cmZ       :: Point c,
        cmT1      :: Point c,
        cmT2      :: Point c,
        cmT3      :: Point c,
        proof1    :: Point c,
        proof2    :: Point c,
        a_xi      :: ScalarField c,
        b_xi      :: ScalarField c,
        c_xi      :: ScalarField c,
        s1_xi     :: ScalarField c,
        s2_xi     :: ScalarField c,
        z_xi      :: ScalarField c,
        l1_xi_mul :: ScalarField c
    }
instance (Show (ScalarField c), Show (BaseField c), EllipticCurve c) => Show (PlonkProof c) where
    show PlonkProof {..} =
        "Proof: "
        ++ show cmA ++ " "
        ++ show cmB ++ " "
        ++ show cmC ++ " "
        ++ show cmZ ++ " "
        ++ show cmT1 ++ " "
        ++ show cmT2 ++ " "
        ++ show cmT3 ++ " "
        ++ show proof1 ++ " "
        ++ show proof2 ++ " "
        ++ show a_xi ++ " "
        ++ show b_xi ++ " "
        ++ show c_xi ++ " "
        ++ show s1_xi ++ " "
        ++ show s2_xi ++ " "
        ++ show z_xi
        ++ show l1_xi_mul
