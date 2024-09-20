{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.Plonkup (
    module ZkFold.Base.Protocol.Plonkup.Internal,
    Plonkup (..)
) where

import           Data.Binary                                         (Binary)
import           Data.Word                                           (Word8)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)
import           Test.QuickCheck                                     (Arbitrary (..), Gen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing (..), PointCompressed)
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

{-| Based on the paper https://eprint.iacr.org/2022/086.pdf -}

instance forall i n l c1 c2 ts core.
        ( KnownNat i
        , KnownNat n
        , KnownNat l
        , KnownNat (PlonkupPermutationSize n)
        , KnownNat (PlonkupPolyExtendedLength n)
        , Ord (BaseField c1)
        , AdditiveGroup (BaseField c1)
        , Pairing c1 c2
        , Arithmetic (ScalarField c1)
        , ToTranscript ts Word8
        , ToTranscript ts (ScalarField c1)
        , ToTranscript ts (PointCompressed c1)
        , FromTranscript ts (ScalarField c1)
        , CoreFunction c1 core
        ) => NonInteractiveProof (Plonkup i n l c1 c2 ts) core where
    type Transcript (Plonkup i n l c1 c2 ts)  = ts
    type SetupProve (Plonkup i n l c1 c2 ts)  = PlonkupProverSetup i n l c1 c2
    type SetupVerify (Plonkup i n l c1 c2 ts) = PlonkupVerifierSetup i n l c1 c2
    type Witness (Plonkup i n l c1 c2 ts)     = (PlonkupWitnessInput i c1, PlonkupProverSecret c1)
    type Input (Plonkup i n l c1 c2 ts)       = PlonkupInput l c1
    type Proof (Plonkup i n l c1 c2 ts)       = PlonkupProof c1

    setupProve :: Plonkup i n l c1 c2 ts -> SetupProve (Plonkup i n l c1 c2 ts)
    setupProve plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupProverSetup {..}

    setupVerify :: Plonkup i n l c1 c2 ts -> SetupVerify (Plonkup i n l c1 c2 ts)
    setupVerify plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupVerifierSetup {..}

    prove :: SetupProve (Plonkup i n l c1 c2 ts) -> Witness (Plonkup i n l c1 c2 ts) -> (Input (Plonkup i n l c1 c2 ts), Proof (Plonkup i n l c1 c2 ts))
    prove setup witness =
        let (input, proof, _) = plonkupProve @i @n @l @c1 @c2 @ts @core setup witness
        in (input, proof)

    verify :: SetupVerify (Plonkup i n l c1 c2 ts) -> Input (Plonkup i n l c1 c2 ts) -> Proof (Plonkup i n l c1 c2 ts) -> Bool
    verify = plonkupVerify @i @n @l @c1 @c2 @ts

instance forall i n l c1 c2 t core.
    ( KnownNat i, KnownNat n, KnownNat l
    , Arithmetic (ScalarField c1), Arbitrary (ScalarField c1), Binary (ScalarField c1)
    , Witness (Plonkup i n l c1 c2 t) ~ (PlonkupWitnessInput i c1, PlonkupProverSecret c1)
    , NonInteractiveProof (Plonkup i n l c1 c2 t) core
    ) => Arbitrary (NonInteractiveProofTestData (Plonkup i n l c1 c2 t) core) where
    arbitrary = do
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest (ScalarField c1) (Vector i) (Vector l))
        let (omega, k1, k2) = getParams $ value @n
        pl <- Plonkup omega k1 k2 ac <$> arbitrary
        secret <- arbitrary
        return $ TestData pl (PlonkupWitnessInput wi, secret)
