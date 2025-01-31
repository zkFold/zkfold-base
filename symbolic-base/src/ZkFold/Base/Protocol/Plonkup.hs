{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.Plonkup (
    module ZkFold.Base.Protocol.Plonkup.Internal,
    Plonkup (..)
) where

import           Data.Binary                                         (Binary)
import           Data.Functor.Rep                                    (Rep, Representable)
import           Data.Word                                           (Word8)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (Compressible (..), CyclicGroup (..), Pairing (..))
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

instance forall p i n l g1 g2 gt ts core.
        ( KnownNat n
        , Representable p
        , Representable i
        , Representable l
        , Foldable l
        , Ord (Rep i)
        , Pairing g1 g2 gt
        , Compressible g1
        , Eq gt
        , Arithmetic (ScalarFieldOf g1)
        , Binary (ScalarFieldOf g2)
        , ToTranscript ts Word8
        , ToTranscript ts (ScalarFieldOf g1)
        , ToTranscript ts (Compressed g1)
        , FromTranscript ts (ScalarFieldOf g1)
        , CoreFunction g1 core
        ) => NonInteractiveProof (Plonkup p i n l g1 g2 ts) core where
    type Transcript (Plonkup p i n l g1 g2 ts)  = ts
    type SetupProve (Plonkup p i n l g1 g2 ts)  = PlonkupProverSetup p i n l g1 g2
    type SetupVerify (Plonkup p i n l g1 g2 ts) = PlonkupVerifierSetup p i n l g1 g2
    type Witness (Plonkup p i n l g1 g2 ts)     = (PlonkupWitnessInput p i g1, PlonkupProverSecret g1)
    type Input (Plonkup p i n l g1 g2 ts)       = PlonkupInput l g1
    type Proof (Plonkup p i n l g1 g2 ts)       = PlonkupProof g1

    setupProve :: Plonkup p i n l g1 g2 ts -> SetupProve (Plonkup p i n l g1 g2 ts)
    setupProve plonk =
        let PlonkupSetup {..} = plonkupSetup @i @p @n @l @g1 @g2 @gt @ts @core plonk
        in PlonkupProverSetup {..}

    setupVerify :: Plonkup p i n l g1 g2 ts -> SetupVerify (Plonkup p i n l g1 g2 ts)
    setupVerify plonk =
        let PlonkupSetup {..} = plonkupSetup @i @p @n @l @g1 @g2 @gt @ts @core plonk
        in PlonkupVerifierSetup {..}

    prove :: SetupProve (Plonkup p i n l g1 g2 ts) -> Witness (Plonkup p i n l g1 g2 ts) -> (Input (Plonkup p i n l g1 g2 ts), Proof (Plonkup p i n l g1 g2 ts))
    prove setup witness =
        let (input, proof, _) = with4n6 @n (plonkupProve @p @i @n @l @g1 @g2 @ts @core setup witness)
        in (input, proof)

    verify :: SetupVerify (Plonkup p i n l g1 g2 ts) -> Input (Plonkup p i n l g1 g2 ts) -> Proof (Plonkup p i n l g1 g2 ts) -> Bool
    verify = with4n6 @n $ plonkupVerify @p @i @n @l @g1 @g2 @gt @ts

