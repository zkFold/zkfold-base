{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.Plonkup (
    module ZkFold.Base.Protocol.Plonkup.Internal,
    Plonk(..)
) where

import           GHC.Generics                                        (Par1)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)
import           Test.QuickCheck                                     (Arbitrary (..), Gen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing (..), Point,
                                                                      PointCompressed)
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Setup
import           ZkFold.Base.Protocol.Plonkup.Utils
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Compiler                            (ArithmeticCircuitTest (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

instance forall i n l c1 c2 t plonk f g1 core.
        ( Plonk i n l c1 c2 t ~ plonk
        , ScalarField c1 ~ f
        , Point c1 ~ g1
        , KnownNat n
        , KnownNat l
        , KnownNat i
        , KnownNat (PlonkPermutationSize n)
        , KnownNat (PlonkPolyExtendedLength n)
        , Arithmetic f
        , Ord (BaseField c1)
        , AdditiveGroup (BaseField c1)
        , Pairing c1 c2
        , ToTranscript t (ScalarField c1)
        , ToTranscript t (PointCompressed c1)
        , FromTranscript t (ScalarField c1)
        , CoreFunction c1 core
        ) => NonInteractiveProof (Plonk i n l c1 c2 t) core where
    type Transcript (Plonk i n l c1 c2 t)  = t
    type SetupProve (Plonk i n l c1 c2 t)  = PlonkupProverSetup i n l c1 c2
    type SetupVerify (Plonk i n l c1 c2 t) = PlonkupVerifierSetup i n l c1 c2
    type Witness (Plonk i n l c1 c2 t)     = (PlonkupWitnessInput i c1, PlonkProverSecret c1)
    type Input (Plonk i n l c1 c2 t)       = PlonkupInput l c1
    type Proof (Plonk i n l c1 c2 t)       = PlonkupProof c1

    setupProve :: plonk -> SetupProve plonk
    setupProve plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupProverSetup {..}

    setupVerify :: plonk -> SetupVerify plonk
    setupVerify plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupVerifierSetup {..}

    prove :: SetupProve plonk -> Witness plonk -> (Input plonk, Proof plonk)
    prove = plonkupProve @i @n @l @c1 @c2 @t @core

    verify :: SetupVerify plonk -> Input plonk -> Proof plonk -> Bool
    verify = plonkupVerify @i @n @l @c1 @c2 @t

instance forall i n l c1 c2 t core . (KnownNat i, KnownNat n, KnownNat l, Arithmetic (ScalarField c1), Arbitrary (ScalarField c1),
        Witness (Plonk i n l c1 c2 t) ~ (PlonkupWitnessInput i c1, PlonkProverSecret c1), NonInteractiveProof (Plonk i n l c1 c2 t) core) => Arbitrary (NonInteractiveProofTestData (Plonk i n l c1 c2 t) core) where
    arbitrary = do
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest (ScalarField c1) (Vector i) Par1)
        vecPubInp <- genSubset (getAllVars ac) (value @l)
        let (omega, k1, k2) = getParams $ value @n
        pl <- Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
        secret <- arbitrary
        return $ TestData pl (PlonkupWitnessInput wi (witnessGenerator ac wi), secret)
