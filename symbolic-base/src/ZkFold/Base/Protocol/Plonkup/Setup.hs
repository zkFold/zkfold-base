{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Setup where

import           Data.Functor.Rep                                  (Rep, Representable)
import           Data.Maybe                                        (fromJust)
import qualified Data.Vector                                       as V
import           GHC.IsList                                        (IsList (..))
import           Prelude                                           hiding (Num (..), drop, length, sum, take, (!!), (/),
                                                                    (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                  (KnownNat, value)
import           ZkFold.Base.Algebra.Basic.Permutations            (fromPermutation)
import           ZkFold.Base.Algebra.EllipticCurve.Class           (EllipticCurve (..), Pairing, Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate        (PolyVec, polyVecInLagrangeBasis, toPolyVec)
import           ZkFold.Base.Protocol.NonInteractiveProof.Internal (CoreFunction (..))
import           ZkFold.Base.Protocol.Plonkup.Internal             (Plonkup (..), PlonkupPermutationSize,
                                                                    PlonkupPolyExtendedLength, with4n6)
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials   (PlonkupCircuitPolynomials (..))
import           ZkFold.Base.Protocol.Plonkup.Relation             (PlonkupRelation (..), toPlonkupRelation)
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments (PlonkupCircuitCommitments (..))
import           ZkFold.Symbolic.Class                             (Arithmetic)

data PlonkupSetup p i n l c1 c2 = PlonkupSetup
    { omega       :: ScalarField c1
    , k1          :: ScalarField c1
    , k2          :: ScalarField c1
    , gs          :: V.Vector (Point c1)
    , h0          :: Point c2
    , h1          :: Point c2
    , sigma1s     :: PolyVec (ScalarField c1) n
    , sigma2s     :: PolyVec (ScalarField c1) n
    , sigma3s     :: PolyVec (ScalarField c1) n
    , relation    :: PlonkupRelation p i n l (ScalarField c1)
    , polynomials :: PlonkupCircuitPolynomials n c1
    , commitments :: PlonkupCircuitCommitments c1
    }

instance
        ( EllipticCurve c1
        , EllipticCurve c2
        , Show (BaseField c1)
        , Show (BaseField c2)
        , Show (ScalarField c1)
        , Show (PlonkupRelation p i n l (ScalarField c1))
        , BooleanOf c1 ~ Bool
        , BooleanOf c2 ~ Bool
        ) => Show (PlonkupSetup p i n l c1 c2) where
    show PlonkupSetup {..} =
        "Setup: "
        ++ show omega ++ " "
        ++ show k1 ++ " "
        ++ show k2 ++ " "
        ++ show gs ++ " "
        ++ show h0 ++ " "
        ++ show h1 ++ " "
        ++ show sigma1s ++ " "
        ++ show sigma2s ++ " "
        ++ show sigma3s ++ " "
        ++ show relation ++ " "
        ++ show polynomials ++ " "
        ++ show commitments

plonkupSetup :: forall i p n l c1 c2 ts core.
    ( KnownNat n
    , Representable l
    , Foldable l
    , Ord (Rep i)
    , Arithmetic (ScalarField c1)
    , Pairing c1 c2
    , CoreFunction c1 core) => Plonkup p i n l c1 c2 ts -> PlonkupSetup p i n l c1 c2
plonkupSetup Plonkup {..} =
    let xs   = fromList $ map (x^) [0 .. (value @n + 5)]
        gs   = fmap (`mul` pointGen) xs
        h0   = pointGen
        h1   = x `mul` pointGen

        relation@PlonkupRelation{..} = fromJust $ toPlonkupRelation ac :: PlonkupRelation p i n l (ScalarField c1)

        f i = case (i-!1) `Prelude.div` value @n of
            0 -> omega^i
            1 -> k1 * (omega^i)
            2 -> k2 * (omega^i)
            _ -> error "setup: invalid index"
        s = fromList $ map f $ fromPermutation @(PlonkupPermutationSize n) $ sigma
        sigma1s = toPolyVec $ V.take (fromIntegral $ value @n) s
        sigma2s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ value @n) s
        sigma3s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ 2 * value @n) s

        qmX = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qM)
        qlX = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qL)
        qrX = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qR)
        qoX = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qO)
        qcX = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qC)
        qkX = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qK)
        s1X = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega sigma1s)
        s2X = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega sigma2s)
        s3X = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega sigma3s)
        tX  = with4n6 @n (polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega t)
        polynomials = PlonkupCircuitPolynomials {..}

        com = msm @c1 @core
        cmQl = gs `com` qlX
        cmQr = gs `com` qrX
        cmQo = gs `com` qoX
        cmQm = gs `com` qmX
        cmQc = gs `com` qcX
        cmQk = gs `com` qkX
        cmS1 = gs `com` s1X
        cmS2 = gs `com` s2X
        cmS3 = gs `com` s3X
        cmT1  = gs `com` tX
        commitments = PlonkupCircuitCommitments {..}

    in PlonkupSetup {..}
