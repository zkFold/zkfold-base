{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Setup where

import           Data.Functor.Rep                                    (Rep, Representable)
import           Data.Maybe                                          (fromJust)
import qualified Data.Vector                                         as V
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations              (fromPermutation)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing, Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Protocol.NonInteractiveProof            (CoreFunction (..))
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..), toPlonkupRelation)
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkupSetup p i n l scalarField g1 g2 = PlonkupSetup
    { omega       :: scalarField
    , k1          :: scalarField
    , k2          :: scalarField
    , gs          :: V.Vector g1
    , h0          :: g2
    , h1          :: g2
    , sigma1s     :: PolyVec scalarField n
    , sigma2s     :: PolyVec scalarField n
    , sigma3s     :: PolyVec scalarField n
    , relation    :: PlonkupRelation p i n l scalarField
    , polynomials :: PlonkupCircuitPolynomials n scalarField
    , commitments :: PlonkupCircuitCommitments g1
    }

instance
        ( Show scalarField
        , Show g1
        , Show g2
        ) => Show (PlonkupSetup p i n l scalarField g1 g2) where
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
    , Representable p
    , Representable i
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
