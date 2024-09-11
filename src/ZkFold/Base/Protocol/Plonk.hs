{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonk (
    Plonk (..)
) where

import           Data.Kind                                           (Type)
import           GHC.Generics                                        (Par1)
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)
import           Test.QuickCheck                                     (Arbitrary (..), Gen)

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Compiler                            (desugarRanges)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data Plonk (i :: Natural) (n :: Natural) (l :: Natural) curve1 curve2 transcript = Plonk {
        omega :: ScalarField curve1,
        k1    :: ScalarField curve1,
        k2    :: ScalarField curve1,
        xPub  :: Vector l (Var (Vector i)),
        ac    :: ArithmeticCircuit (ScalarField curve1) (Vector i) Par1,
        x     :: ScalarField curve1
    }

fromPlonkup :: 
    ( KnownNat i
    , Arithmetic (ScalarField c1)
    ) => Plonkup i n l c1 c2 ts -> Plonk i n l c1 c2 ts
fromPlonkup Plonkup {..} = Plonk { ac = desugarRanges ac, ..}

toPlonkup :: Plonk i n l c1 c2 ts -> Plonkup i n l c1 c2 ts
toPlonkup Plonk {..} = Plonkup {..}

instance Show (Plonkup i n l c1 c2 t) => Show (Plonk i n l c1 c2 t) where
    show = show . toPlonkup

instance (KnownNat i, Arithmetic (ScalarField c1), Arbitrary (Plonkup i n l c1 c2 t))
        => Arbitrary (Plonk i n l c1 c2 t) where
    arbitrary = fromPlonkup <$> arbitrary

instance forall i n l c1 c2 (ts :: Type) core .
        ( NonInteractiveProof (Plonkup i n l c1 c2 ts) core
        , SetupProve (Plonkup i n l c1 c2 ts) ~ PlonkupProverSetup i n l c1 c2
        , SetupVerify (Plonkup i n l c1 c2 ts) ~ PlonkupVerifierSetup i n l c1 c2
        , Witness (Plonkup i n l c1 c2 ts) ~ (PlonkupWitnessInput i c1, PlonkupProverSecret c1)
        , Input (Plonkup i n l c1 c2 ts) ~ PlonkupInput l c1
        , Proof (Plonkup i n l c1 c2 ts) ~ PlonkupProof c1
        ) => NonInteractiveProof (Plonk i n l c1 c2 ts) core where
    type Transcript (Plonk i n l c1 c2 ts)  = ts
    type SetupProve (Plonk i n l c1 c2 ts)  = PlonkupProverSetup i n l c1 c2
    type SetupVerify (Plonk i n l c1 c2 ts) = PlonkupVerifierSetup i n l c1 c2
    type Witness (Plonk i n l c1 c2 ts)     = (PlonkupWitnessInput i c1, PlonkupProverSecret c1)
    type Input (Plonk i n l c1 c2 ts)       = PlonkupInput l c1
    type Proof (Plonk i n l c1 c2 ts)       = PlonkupProof c1

    setupProve :: Plonk i n l c1 c2 ts -> SetupProve (Plonk i n l c1 c2 ts)
    setupProve = setupProve @(Plonkup i n l c1 c2 ts) @core . toPlonkup

    setupVerify :: Plonk i n l c1 c2 ts -> SetupVerify (Plonk i n l c1 c2 ts)
    setupVerify = setupVerify @(Plonkup i n l c1 c2 ts) @core . toPlonkup

    prove :: SetupProve (Plonk i n l c1 c2 ts) -> Witness (Plonk i n l c1 c2 ts) -> (Input (Plonk i n l c1 c2 ts), Proof (Plonk i n l c1 c2 ts))
    prove = prove @(Plonkup i n l c1 c2 ts) @core

    verify :: SetupVerify (Plonk i n l c1 c2 ts) -> Input (Plonk i n l c1 c2 ts) -> Proof (Plonk i n l c1 c2 ts) -> Bool
    verify = verify @(Plonkup i n l c1 c2 ts) @core

instance forall i n l c1 c2 t core . (KnownNat i, Arithmetic (ScalarField c1),
            Witness (Plonk i n l c1 c2 t) ~ Witness (Plonkup i n l c1 c2 t), NonInteractiveProof (Plonk i n l c1 c2 t) core
    , Arbitrary (NonInteractiveProofTestData (Plonkup i n l c1 c2 t) core))
        => Arbitrary (NonInteractiveProofTestData (Plonk i n l c1 c2 t) core) where
    arbitrary = do
        TestData plonkup w <- arbitrary :: Gen (NonInteractiveProofTestData (Plonkup i n l c1 c2 t) core)
        return $ TestData (fromPlonkup plonkup) w
