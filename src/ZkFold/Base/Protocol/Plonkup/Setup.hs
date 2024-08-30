{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Setup where

import           Data.Maybe                                          (fromJust)
import qualified Data.Vector                                         as V
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations              (fromPermutation)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Point, Pairing)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.NonInteractiveProof            (CoreFunction(..))
import           ZkFold.Base.Protocol.Plonkup.Internal               (Plonk(..))
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..), toPlonkupRelation)
import           ZkFold.Base.Protocol.Plonkup.Utils
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkupSetup i n l c1 c2 = PlonkupSetup
    { omega       :: ScalarField c1
    , k1          :: ScalarField c1
    , k2          :: ScalarField c1
    , iPub        :: Vector l (Var (Vector i))
    , gs          :: V.Vector (Point c1)
    , h0          :: Point c2
    , h1          :: Point c2
    , sigma1s     :: PolyVec (ScalarField c1) n
    , sigma2s     :: PolyVec (ScalarField c1) n
    , sigma3s     :: PolyVec (ScalarField c1) n
    , relation    :: PlonkupRelation n i (ScalarField c1)
    , polynomials :: PlonkCircuitPolynomials n c1
    , commitments :: PlonkCircuitCommitments c1
    }

instance
        ( EllipticCurve c1
        , EllipticCurve c2
        , Show (BaseField c1)
        , Show (BaseField c2)
        , Show (ScalarField c1)
        , Show (PlonkupRelation n i (ScalarField c1))
        ) => Show (PlonkupSetup i n l c1 c2) where
    show PlonkupSetup {..} =
        "Setup: "
        ++ show omega ++ " "
        ++ show k1 ++ " "
        ++ show k2 ++ " "
        ++ show iPub ++ " "
        ++ show gs ++ " "
        ++ show h0 ++ " "
        ++ show h1 ++ " "
        ++ show sigma1s ++ " "
        ++ show sigma2s ++ " "
        ++ show sigma3s ++ " "
        ++ show relation ++ " "
        ++ show polynomials ++ " "
        ++ show commitments

plonkupSetup :: forall i n l c1 c2 ts core.
    ( KnownNat i
    , KnownNat l
    , KnownNat n
    , KnownNat (PlonkPermutationSize n)
    , KnownNat (PlonkPolyExtendedLength n)
    , Arithmetic (ScalarField c1)
    , Pairing c1 c2
    , CoreFunction c1 core) => Plonk i n l c1 c2 ts -> PlonkupSetup i n l c1 c2
plonkupSetup Plonk {..} =
    let xs   = fromList $ map (x^) [0 .. (value @n + 5)]
        gs   = fmap (`mul` gen) xs
        h0   = gen
        h1   = x `mul` gen

        relation@PlonkupRelation{..} = fromJust $ toPlonkupRelation iPub ac :: PlonkupRelation n i (ScalarField c1)

        f i = case (i-!1) `Prelude.div` value @n of
            0 -> omega^i
            1 -> k1 * (omega^i)
            2 -> k2 * (omega^i)
            _ -> error "setup: invalid index"
        s = fromList $ map f $ fromPermutation @(PlonkPermutationSize n) $ sigma
        sigma1s = toPolyVec $ V.take (fromIntegral $ value @n) s
        sigma2s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ value @n) s
        sigma3s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ 2 * value @n) s

        qm     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qM
        ql     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qL
        qr     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qR
        qo     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qO
        qc     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qC
        qk     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qK
        sigma1 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega sigma1s
        sigma2 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega sigma2s
        sigma3 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega sigma3s
        polynomials = PlonkCircuitPolynomials {..}

        com = msm @c1 @core
        cmQl = gs `com` ql
        cmQr = gs `com` qr
        cmQo = gs `com` qo
        cmQm = gs `com` qm
        cmQc = gs `com` qc
        cmQk = gs `com` qk
        cmS1 = gs `com` sigma1
        cmS2 = gs `com` sigma2
        cmS3 = gs `com` sigma3
        commitments = PlonkCircuitCommitments {..}

    in PlonkupSetup {..}
