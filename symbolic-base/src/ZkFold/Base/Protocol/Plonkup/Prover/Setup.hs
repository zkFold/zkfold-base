{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Setup where

import qualified Data.Vector                                     as V
import           Prelude                                         hiding (Num (..), drop, length, sum, take, (!!), (/),
                                                                  (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class         (EllipticCurve (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate      hiding (qr)
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
import           ZkFold.Base.Protocol.Plonkup.Relation           (PlonkupRelation (..))

data PlonkupProverSetup p i n l c1 c2 = PlonkupProverSetup
    { omega       :: ScalarField c1
    , k1          :: ScalarField c1
    , k2          :: ScalarField c1
    , gs          :: V.Vector (Point c1)
    , sigma1s     :: PolyVec (ScalarField c1) n
    , sigma2s     :: PolyVec (ScalarField c1) n
    , sigma3s     :: PolyVec (ScalarField c1) n
    , relation    :: PlonkupRelation p i n l (ScalarField c1)
    , polynomials :: PlonkupCircuitPolynomials n c1
    }

instance
        ( EllipticCurve c1
        , EllipticCurve c2
        , Show (BaseField c1)
        , Show (BaseField c2)
        , Show (ScalarField c1)
        , Show (PlonkupRelation p i n l (ScalarField c1))
        ) => Show (PlonkupProverSetup p i n l c1 c2) where
    show PlonkupProverSetup {..} =
        "Prover setup: "
        ++ show omega ++ " "
        ++ show k1 ++ " "
        ++ show k2 ++ " "
        ++ show gs ++ " "
        ++ show sigma1s ++ " "
        ++ show sigma2s ++ " "
        ++ show sigma3s ++ " "
        ++ show relation ++ " "
        ++ show polynomials
