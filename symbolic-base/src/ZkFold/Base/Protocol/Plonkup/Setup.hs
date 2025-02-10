{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Setup where

import           Data.Binary                                       (Binary)
import           Data.Functor.Rep                                  (Rep, Representable)
import           Data.Maybe                                        (fromJust)
import qualified Data.Vector                                       as V
import           GHC.IsList                                        (IsList (..))
import           Prelude                                           hiding (Num (..), drop, length, sum, take, (!!), (/),
                                                                    (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                  (KnownNat, value)
import           ZkFold.Base.Algebra.Basic.Permutations            (fromPermutation)
import           ZkFold.Base.Algebra.EllipticCurve.Class           (CyclicGroup (..), Pairing)
import           ZkFold.Base.Algebra.Polynomials.Univariate        (PolyVec, polyVecInLagrangeBasis, toPolyVec)
import           ZkFold.Base.Data.Vector                           (Vector (..))
import           ZkFold.Base.Protocol.NonInteractiveProof.Internal (CoreFunction (..))
import           ZkFold.Base.Protocol.Plonkup.Internal             (Plonkup (..), PlonkupPermutationSize,
                                                                    PlonkupPolyExtendedLength, with4n6)
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials   (PlonkupCircuitPolynomials (..))
import           ZkFold.Base.Protocol.Plonkup.Relation             (PlonkupRelation (..), toPlonkupRelation)
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments (PlonkupCircuitCommitments (..))
import           ZkFold.Symbolic.Class                             (Arithmetic)

data PlonkupSetup p i n l g1 g2 = PlonkupSetup
    { omega       :: ScalarFieldOf g1
    , k1          :: ScalarFieldOf g1
    , k2          :: ScalarFieldOf g1
    , gs          :: V.Vector g1
    , h0          :: g2
    , h1          :: g2
    , sigma1s     :: PolyVec (ScalarFieldOf g1) n
    , sigma2s     :: PolyVec (ScalarFieldOf g1) n
    , sigma3s     :: PolyVec (ScalarFieldOf g1) n
    , relation    :: PlonkupRelation p i n l (ScalarFieldOf g1)
    , polynomials :: PlonkupCircuitPolynomials n g1
    , commitments :: PlonkupCircuitCommitments g1
    }

instance
        ( Show g1
        , Show g2
        , Show (ScalarFieldOf g1)
        , Show (PlonkupRelation p i n l (ScalarFieldOf g1))
        ) => Show (PlonkupSetup p i n l g1 g2) where
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

plonkupSetup :: forall i p n l g1 g2 gt ts core.
    ( KnownNat n
    , Representable p
    , Representable i
    , Representable l
    , Foldable l
    , Ord (Rep i)
    , Arithmetic (ScalarFieldOf g1)
    , Binary (ScalarFieldOf g2)
    , Pairing g1 g2 gt
    , CoreFunction g1 core) => Plonkup p i n l g1 g2 ts -> PlonkupSetup p i n l g1 g2
plonkupSetup Plonkup {..} =
    let gs = toV gs'
        h0 = pointGen

        relation@PlonkupRelation{..} = fromJust $ toPlonkupRelation ac :: PlonkupRelation p i n l (ScalarFieldOf g1)

        f i = case (i-!1) `Prelude.div` value @n of
            0 -> omega^i
            1 -> k1 * (omega^i)
            2 -> k2 * (omega^i)
            _ -> error "setup: invalid index"
        s = fromList $ map f $ fromPermutation @(PlonkupPermutationSize n) $ sigma
        sigma1s = toPolyVec $ V.take (fromIntegral $ value @n) s
        sigma2s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ value @n) s
        sigma3s = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ 2 * value @n) s

        qmX = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega qM)
        qlX = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega qL)
        qrX = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega qR)
        qoX = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega qO)
        qcX = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega qC)
        qkX = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega qK)
        s1X = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega sigma1s)
        s2X = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega sigma2s)
        s3X = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega sigma3s)
        tX  = with4n6 @n (polyVecInLagrangeBasis @(ScalarFieldOf g1) @n @(PlonkupPolyExtendedLength n) omega t)
        polynomials = PlonkupCircuitPolynomials {..}

        com = msm @g1 @core
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
