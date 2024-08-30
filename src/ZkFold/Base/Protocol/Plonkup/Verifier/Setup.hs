{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier.Setup where

import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments   (PlonkCircuitCommitments (..))

data PlonkupVerifierSetup i n l c1 c2 = PlonkupVerifierSetup
    { omega       :: ScalarField c1
    , k1          :: ScalarField c1
    , k2          :: ScalarField c1
    , iPub        :: Vector l (Var (Vector i))
    , h1          :: Point c2
    , sigma1s     :: PolyVec (ScalarField c1) n
    , sigma2s     :: PolyVec (ScalarField c1) n
    , sigma3s     :: PolyVec (ScalarField c1) n
    , relation    :: PlonkupRelation n i (ScalarField c1)
    , commitments :: PlonkCircuitCommitments c1
    }

instance
        ( EllipticCurve c1
        , EllipticCurve c2
        , Show (BaseField c1)
        , Show (BaseField c2)
        , Show (ScalarField c1)
        , Show (PlonkupRelation n i (ScalarField c1))
        ) => Show (PlonkupVerifierSetup i n l c1 c2) where
    show PlonkupVerifierSetup {..} =
        "Verifier setup: "
        ++ show omega ++ " "
        ++ show k1 ++ " "
        ++ show k2 ++ " "
        ++ show iPub ++ " "
        ++ show h1 ++ " "
        ++ show sigma1s ++ " "
        ++ show sigma2s ++ " "
        ++ show sigma3s ++ " "
        ++ show relation ++ " "
        ++ show commitments
