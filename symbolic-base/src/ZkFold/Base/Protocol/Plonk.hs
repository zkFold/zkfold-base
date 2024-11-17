{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonk (
    Plonk (..)
) where

import           Data.Binary                                         (Binary)
import           Data.Functor.Rep                                    (Rep)
import           Data.Kind                                           (Type)
import           Data.Word                                           (Word8)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class                     (AdditiveGroup)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing, PointCompressed)
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonk.Prover                   (plonkProve)
import           ZkFold.Base.Protocol.Plonk.Verifier                 (plonkVerify)
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Compiler                            (desugarRanges)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

{-| Based on the paper https://eprint.iacr.org/2019/953.pdf -}

data Plonk (i :: Natural) p (n :: Natural) (l :: Natural) curve1 curve2 transcript = Plonk {
        omega :: ScalarField curve1,
        k1    :: ScalarField curve1,
        k2    :: ScalarField curve1,
        ac    :: ArithmeticCircuit (ScalarField curve1) p (Vector i) (Vector l),
        x     :: ScalarField curve1
    }

fromPlonkup ::
    ( KnownNat i
    , Arithmetic (ScalarField c1)
    , Binary (ScalarField c1)
    , Binary (Rep p)
    ) => Plonkup i p n l c1 c2 ts -> Plonk i p n l c1 c2 ts
fromPlonkup Plonkup {..} = Plonk { ac = desugarRanges ac, ..}

toPlonkup :: Plonk i p n l c1 c2 ts -> Plonkup i p n l c1 c2 ts
toPlonkup Plonk {..} = Plonkup {..}

instance (Show (ScalarField c1), Arithmetic (ScalarField c1), KnownNat l, KnownNat i) => Show (Plonk i p n l c1 c2 t) where
    show Plonk {..} =
        "Plonk: " ++ show omega ++ " " ++ show k1 ++ " " ++ show k2 ++ " " ++ show (acOutput ac) ++ " " ++ show ac ++ " " ++ show x

instance ( KnownNat i, Arithmetic (ScalarField c1)
         , Binary (ScalarField c1), Binary (Rep p)
         , Arbitrary (Plonkup i p n l c1 c2 t))
        => Arbitrary (Plonk i p n l c1 c2 t) where
    arbitrary = fromPlonkup <$> arbitrary

instance forall i p n l c1 c2 (ts :: Type) core .
        ( NonInteractiveProof (Plonkup i p n l c1 c2 ts) core
        , SetupProve (Plonkup i p n l c1 c2 ts) ~ PlonkupProverSetup p i n l c1 c2
        , SetupVerify (Plonkup i p n l c1 c2 ts) ~ PlonkupVerifierSetup p i n l c1 c2
        , Witness (Plonkup i p n l c1 c2 ts) ~ (PlonkupWitnessInput p i c1, PlonkupProverSecret c1)
        , Input (Plonkup i p n l c1 c2 ts) ~ PlonkupInput l c1
        , Proof (Plonkup i p n l c1 c2 ts) ~ PlonkupProof c1
        , KnownNat n
        , Ord (BaseField c1)
        , AdditiveGroup (BaseField c1)
        , Pairing c1 c2
        , Arithmetic (ScalarField c1)
        , ToTranscript ts Word8
        , ToTranscript ts (ScalarField c1)
        , ToTranscript ts (PointCompressed c1)
        , FromTranscript ts (ScalarField c1)
        , CoreFunction c1 core
        ) => NonInteractiveProof (Plonk i p n l c1 c2 ts) core where
    type Transcript (Plonk i p n l c1 c2 ts)  = ts
    type SetupProve (Plonk i p n l c1 c2 ts)  = PlonkupProverSetup p i n l c1 c2
    type SetupVerify (Plonk i p n l c1 c2 ts) = PlonkupVerifierSetup p i n l c1 c2
    type Witness (Plonk i p n l c1 c2 ts)     = (PlonkupWitnessInput p i c1, PlonkupProverSecret c1)
    type Input (Plonk i p n l c1 c2 ts)       = PlonkupInput l c1
    type Proof (Plonk i p n l c1 c2 ts)       = PlonkupProof c1

    setupProve :: Plonk i p n l c1 c2 ts -> SetupProve (Plonk i p n l c1 c2 ts)
    setupProve = setupProve @(Plonkup i p n l c1 c2 ts) @core . toPlonkup

    setupVerify :: Plonk i p n l c1 c2 ts -> SetupVerify (Plonk i p n l c1 c2 ts)
    setupVerify = setupVerify @(Plonkup i p n l c1 c2 ts) @core . toPlonkup

    prove :: SetupProve (Plonk i p n l c1 c2 ts) -> Witness (Plonk i p n l c1 c2 ts) -> (Input (Plonk i p n l c1 c2 ts), Proof (Plonk i p n l c1 c2 ts))
    prove setup witness =
        let (input, proof, _) = plonkProve @p @i @n @l @c1 @c2 @ts @core setup witness
        in (input, proof)

    verify :: SetupVerify (Plonk i p n l c1 c2 ts) -> Input (Plonk i p n l c1 c2 ts) -> Proof (Plonk i p n l c1 c2 ts) -> Bool
    verify = plonkVerify @p @i @n @l @c1 @c2 @ts
