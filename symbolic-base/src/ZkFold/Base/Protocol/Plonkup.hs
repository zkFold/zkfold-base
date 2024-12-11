{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.Plonkup (
    module ZkFold.Base.Protocol.Plonkup.Internal,
    Plonkup (..)
) where

import           Data.Functor.Rep                                    (Rep, Representable)
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
import qualified ZkFold.Symbolic.Data.Ord                            as Sym

{-| Based on the paper https://eprint.iacr.org/2022/086.pdf -}

instance forall p i n l c1 c2 ts core.
        ( KnownNat n
        , Representable p
        , Representable i
        , Representable l
        , Foldable l
        , Ord (Rep i)
        , Sym.Ord (BooleanOf c1) (BaseField c1)
        , AdditiveGroup (BaseField c1)
        , Pairing c1 c2
        , Arithmetic (ScalarField c1)
        , ToTranscript ts Word8
        , ToTranscript ts (ScalarField c1)
        , ToTranscript ts (PointCompressed c1)
        , FromTranscript ts (ScalarField c1)
        , CoreFunction c1 core
        ) => NonInteractiveProof (Plonkup p i n l c1 c2 ts) core where
    type Transcript (Plonkup p i n l c1 c2 ts)  = ts
    type SetupProve (Plonkup p i n l c1 c2 ts)  = PlonkupProverSetup p i n l c1 c2
    type SetupVerify (Plonkup p i n l c1 c2 ts) = PlonkupVerifierSetup p i n l c1 c2
    type Witness (Plonkup p i n l c1 c2 ts)     = (PlonkupWitnessInput p i c1, PlonkupProverSecret c1)
    type Input (Plonkup p i n l c1 c2 ts)       = PlonkupInput l c1
    type Proof (Plonkup p i n l c1 c2 ts)       = PlonkupProof c1

    setupProve :: Plonkup p i n l c1 c2 ts -> SetupProve (Plonkup p i n l c1 c2 ts)
    setupProve plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupProverSetup {..}

    setupVerify :: Plonkup p i n l c1 c2 ts -> SetupVerify (Plonkup p i n l c1 c2 ts)
    setupVerify plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupVerifierSetup {..}

    prove :: SetupProve (Plonkup p i n l c1 c2 ts) -> Witness (Plonkup p i n l c1 c2 ts) -> (Input (Plonkup p i n l c1 c2 ts), Proof (Plonkup p i n l c1 c2 ts))
    prove setup witness =
        let (input, proof, _) = with4n6 @n (plonkupProve @p @i @n @l @c1 @c2 @ts @core setup witness)
        in (input, proof)

    verify :: SetupVerify (Plonkup p i n l c1 c2 ts) -> Input (Plonkup p i n l c1 c2 ts) -> Proof (Plonkup p i n l c1 c2 ts) -> Bool
    verify = with4n6 @n $ plonkupVerify @p @i @n @l @c1 @c2 @ts

