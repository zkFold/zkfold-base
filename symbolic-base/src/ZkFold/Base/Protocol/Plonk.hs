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

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.Vector                             (Vector)
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

data Plonk p i (n :: Natural) l g1 g2 transcript = Plonk {
        omega :: ScalarFieldOf g1,
        k1    :: ScalarFieldOf g1,
        k2    :: ScalarFieldOf g1,
        ac    :: ArithmeticCircuit (ScalarFieldOf g1) p i l,
        h1    :: g2,
        gs'   :: Vector (n + 5) g1
    }

fromPlonkup ::
    ( Arithmetic (ScalarFieldOf g1)
    , Binary (ScalarFieldOf g1)
    , Binary (Rep p)
    , Binary (Rep i)
    , Ord (Rep i)
    ) => Plonkup p i n l g1 g2 ts -> Plonk p i n l g1 g2 ts
fromPlonkup Plonkup {..} = Plonk { ac = desugarRanges ac, ..}

toPlonkup :: Plonk p i n l g1 g2 ts -> Plonkup p i n l g1 g2 ts
toPlonkup Plonk {..} = Plonkup {..}

instance (Show1 l, Show (Rep i), Show (ScalarFieldOf g1), Ord (Rep i), Show g1, Show g2) => Show (Plonk p i n l g1 g2 t) where
    show Plonk {..} =
        "Plonk: " ++ show omega ++ " " ++ show k1 ++ " " ++ show k2 ++ " " ++ show (acOutput ac) ++ " " ++ show ac ++ " " ++ show h1 ++ " " ++ show gs'

instance ( Arithmetic (ScalarFieldOf g1), Binary (ScalarFieldOf g1)
         , Binary (Rep p), Binary (Rep i), Ord (Rep i)
         , Arbitrary (Plonkup p i n l g1 g2 t))
        => Arbitrary (Plonk p i n l g1 g2 t) where
    arbitrary = fromPlonkup <$> arbitrary

instance forall p i n l g1 g2 gt (ts :: Type) core .
        ( NonInteractiveProof (Plonkup p i n l g1 g2 ts) core
        , SetupProve (Plonkup p i n l g1 g2 ts) ~ PlonkupProverSetup p i n l g1 g2
        , SetupVerify (Plonkup p i n l g1 g2 ts) ~ PlonkupVerifierSetup p i n l g1 g2
        , Witness (Plonkup p i n l g1 g2 ts) ~ (PlonkupWitnessInput p i g1, PlonkupProverSecret g1)
        , Input (Plonkup p i n l g1 g2 ts) ~ PlonkupInput l g1
        , Proof (Plonkup p i n l g1 g2 ts) ~ PlonkupProof g1
        , KnownNat n
        , Foldable l
        , Compressible g1
        , Pairing g1 g2 gt
        , Eq gt
        , Arithmetic (ScalarFieldOf g1)
        , ToTranscript ts Word8
        , ToTranscript ts (ScalarFieldOf g1)
        , ToTranscript ts (Compressed g1)
        , FromTranscript ts (ScalarFieldOf g1)
        , CoreFunction g1 core
        ) => NonInteractiveProof (Plonk p i n l g1 g2 ts) core where
    type Transcript (Plonk p i n l g1 g2 ts)  = ts
    type SetupProve (Plonk p i n l g1 g2 ts)  = PlonkupProverSetup p i n l g1 g2
    type SetupVerify (Plonk p i n l g1 g2 ts) = PlonkupVerifierSetup p i n l g1 g2
    type Witness (Plonk p i n l g1 g2 ts)     = (PlonkupWitnessInput p i g1, PlonkupProverSecret g1)
    type Input (Plonk p i n l g1 g2 ts)       = PlonkupInput l g1
    type Proof (Plonk p i n l g1 g2 ts)       = PlonkupProof g1

    setupProve :: Plonk p i n l g1 g2 ts -> SetupProve (Plonk p i n l g1 g2 ts)
    setupProve = setupProve @(Plonkup p i n l g1 g2 ts) @core . toPlonkup

    setupVerify :: Plonk p i n l g1 g2 ts -> SetupVerify (Plonk p i n l g1 g2 ts)
    setupVerify = setupVerify @(Plonkup p i n l g1 g2 ts) @core . toPlonkup

    prove :: SetupProve (Plonk p i n l g1 g2 ts) -> Witness (Plonk p i n l g1 g2 ts) -> (Input (Plonk p i n l g1 g2 ts), Proof (Plonk p i n l g1 g2 ts))
    prove setup witness =
        let (input, proof, _) = plonkProve @p @i @n @l @g1 @g2 @ts @core setup witness
        in (input, proof)

    verify :: SetupVerify (Plonk p i n l g1 g2 ts) -> Input (Plonk p i n l g1 g2 ts) -> Proof (Plonk p i n l g1 g2 ts) -> Bool
    verify = plonkVerify @p @i @n @l @g1 @g2 @gt @ts
