{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonk (
    Plonk (..)
) where

import           Data.Binary                                         (Binary)
import           Data.Functor.Classes                                (Show1)
import           Data.Functor.Rep                                    (Rep)
import           Data.Kind                                           (Type)
import           Data.Word                                           (Word8)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class                     (AdditiveGroup)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
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
import qualified ZkFold.Symbolic.Data.Ord                            as Sym

{-| Based on the paper https://eprint.iacr.org/2019/953.pdf -}

data Plonk p i (n :: Natural) l curve1 curve2 transcript = Plonk {
        omega :: ScalarField curve1,
        k1    :: ScalarField curve1,
        k2    :: ScalarField curve1,
        ac    :: ArithmeticCircuit (ScalarField curve1) p i l,
        x     :: ScalarField curve1
    }

fromPlonkup ::
    ( Arithmetic (ScalarField c1)
    , Binary (ScalarField c1)
    , Binary (Rep p)
    , Binary (Rep i)
    , Ord (Rep i)
    ) => Plonkup p i n l c1 c2 ts -> Plonk p i n l c1 c2 ts
fromPlonkup Plonkup {..} = Plonk { ac = desugarRanges ac, ..}

toPlonkup :: Plonk p i n l c1 c2 ts -> Plonkup p i n l c1 c2 ts
toPlonkup Plonk {..} = Plonkup {..}

instance (Show1 l, Show (Rep i), Show (ScalarField c1), Ord (Rep i)) => Show (Plonk p i n l c1 c2 t) where
    show Plonk {..} =
        "Plonk: " ++ show omega ++ " " ++ show k1 ++ " " ++ show k2 ++ " " ++ show (acOutput ac) ++ " " ++ show ac ++ " " ++ show x

instance ( Arithmetic (ScalarField c1), Binary (ScalarField c1)
         , Binary (Rep p), Binary (Rep i), Ord (Rep i)
         , Arbitrary (Plonkup p i n l c1 c2 t))
        => Arbitrary (Plonk p i n l c1 c2 t) where
    arbitrary = fromPlonkup <$> arbitrary

instance forall p i n l c1 c2 (ts :: Type) core .
        ( NonInteractiveProof (Plonkup p i n l c1 c2 ts) core
        , SetupProve (Plonkup p i n l c1 c2 ts) ~ PlonkupProverSetup p i n l c1 c2
        , SetupVerify (Plonkup p i n l c1 c2 ts) ~ PlonkupVerifierSetup p i n l c1 c2
        , Witness (Plonkup p i n l c1 c2 ts) ~ (PlonkupWitnessInput p i c1, PlonkupProverSecret c1)
        , Input (Plonkup p i n l c1 c2 ts) ~ PlonkupInput l c1
        , Proof (Plonkup p i n l c1 c2 ts) ~ PlonkupProof c1
        , KnownNat n
        , Foldable l
        , Sym.Ord (BooleanOf c1) (BaseField c1)
        , AdditiveGroup (BaseField c1)
        , Pairing c1 c2
        , Arithmetic (ScalarField c1)
        , ToTranscript ts Word8
        , ToTranscript ts (ScalarField c1)
        , ToTranscript ts (PointCompressed c1)
        , FromTranscript ts (ScalarField c1)
        , CoreFunction c1 core
        ) => NonInteractiveProof (Plonk p i n l c1 c2 ts) core where
    type Transcript (Plonk p i n l c1 c2 ts)  = ts
    type SetupProve (Plonk p i n l c1 c2 ts)  = PlonkupProverSetup p i n l c1 c2
    type SetupVerify (Plonk p i n l c1 c2 ts) = PlonkupVerifierSetup p i n l c1 c2
    type Witness (Plonk p i n l c1 c2 ts)     = (PlonkupWitnessInput p i c1, PlonkupProverSecret c1)
    type Input (Plonk p i n l c1 c2 ts)       = PlonkupInput l c1
    type Proof (Plonk p i n l c1 c2 ts)       = PlonkupProof c1

    setupProve :: Plonk p i n l c1 c2 ts -> SetupProve (Plonk p i n l c1 c2 ts)
    setupProve = setupProve @(Plonkup p i n l c1 c2 ts) @core . toPlonkup

    setupVerify :: Plonk p i n l c1 c2 ts -> SetupVerify (Plonk p i n l c1 c2 ts)
    setupVerify = setupVerify @(Plonkup p i n l c1 c2 ts) @core . toPlonkup

    prove :: SetupProve (Plonk p i n l c1 c2 ts) -> Witness (Plonk p i n l c1 c2 ts) -> (Input (Plonk p i n l c1 c2 ts), Proof (Plonk p i n l c1 c2 ts))
    prove setup witness =
        let (input, proof, _) = plonkProve @p @i @n @l @c1 @c2 @ts @core setup witness
        in (input, proof)

    verify :: SetupVerify (Plonk p i n l c1 c2 ts) -> Input (Plonk p i n l c1 c2 ts) -> Proof (Plonk p i n l c1 c2 ts) -> Bool
    verify = plonkVerify @p @i @n @l @c1 @c2 @ts
