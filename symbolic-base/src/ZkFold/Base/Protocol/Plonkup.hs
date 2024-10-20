{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.Plonkup (
    module ZkFold.Base.Protocol.Plonkup.Internal,
    Plonkup (..)
) where

import           Data.Word                                           (Word8)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing (..), PointCompressed)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Setup
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

{-| Based on the paper https://eprint.iacr.org/2022/086.pdf -}

instance forall i n l c1 c2 ts core.
        ( KnownNat i
        , KnownNat n
        , KnownNat l
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
        let (input, proof, _) = with4n6 @n (plonkupProve @i @n @l @c1 @c2 @ts @core setup witness)
        in (input, proof)

    verify :: SetupVerify (Plonkup i n l c1 c2 ts) -> Input (Plonkup i n l c1 c2 ts) -> Proof (Plonkup i n l c1 c2 ts) -> Bool
    verify = with4n6 @n $ plonkupVerify @i @n @l @c1 @c2 @ts

