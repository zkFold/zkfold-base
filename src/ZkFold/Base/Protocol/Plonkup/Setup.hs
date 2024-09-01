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
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing, Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.NonInteractiveProof            (CoreFunction (..))
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..), toPlonkupRelation)
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkupSetup i n l c1 c2 = PlonkupSetup
    { omega       :: ScalarField c1
    , k1          :: ScalarField c1
    , k2          :: ScalarField c1
    , xPub        :: Vector l (Var (Vector i))
    , gs          :: V.Vector (Point c1)
    , h0          :: Point c2
    , h1          :: Point c2
    , sigma1s     :: PolyVec (ScalarField c1) n
    , sigma2s     :: PolyVec (ScalarField c1) n
    , sigma3s     :: PolyVec (ScalarField c1) n
    , relation    :: PlonkupRelation i n l (ScalarField c1)
    , polynomials :: PlonkupCircuitPolynomials n c1
    , commitments :: PlonkupCircuitCommitments c1
    }

instance
        ( EllipticCurve c1
        , EllipticCurve c2
        , Show (BaseField c1)
        , Show (BaseField c2)
        , Show (ScalarField c1)
        , Show (PlonkupRelation i n l (ScalarField c1))
        ) => Show (PlonkupSetup i n l c1 c2) where
    show PlonkupSetup {..} =
        "Setup: "
        ++ show omega ++ " "
        ++ show k1 ++ " "
        ++ show k2 ++ " "
        ++ show xPub ++ " "
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
    , KnownNat (PlonkupPermutationSize n)
    , KnownNat (PlonkupPolyExtendedLength n)
    , Arithmetic (ScalarField c1)
    , Pairing c1 c2
    , CoreFunction c1 core) => Plonkup i n l c1 c2 ts -> PlonkupSetup i n l c1 c2
plonkupSetup Plonkup {..} =
    let xs   = fromList $ map (x^) [0 .. (value @n + 5)]
        gs   = fmap (`mul` gen) xs
        h0   = gen
        h1   = x `mul` gen

        relation@PlonkupRelation{..} = fromJust $ toPlonkupRelation xPub ac :: PlonkupRelation i n l (ScalarField c1)

        f i = case (i-!1) `Prelude.div` value @n of
            0 -> omega^i
            1 -> k1 * (omega^i)
            2 -> k2 * (omega^i)
            _ -> error "setup: invalid index"
        s = fromList $ map f $ fromPermutation @(PlonkupPermutationSize n) $ sigma
        sigma1s = toPolyVec $ V.take (fromIntegral $ value @n) s
        sigma2s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ value @n) s
        sigma3s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ 2 * value @n) s

        qm     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qM
        ql     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qL
        qr     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qR
        qo     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qO
        qc     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qC
        qk     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega qK
        sigma1 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega sigma1s
        sigma2 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega sigma2s
        sigma3 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega sigma3s
        polynomials = PlonkupCircuitPolynomials {..}

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
        commitments = PlonkupCircuitCommitments {..}

    in PlonkupSetup {..}
