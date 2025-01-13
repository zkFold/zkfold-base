{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Setup where

import qualified Data.Vector                                     as V
import           Prelude                                         hiding (Num (..), drop, length, sum, take, (!!), (/),
                                                                  (^))

import           ZkFold.Base.Algebra.Polynomials.Univariate      hiding (qr)
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
import           ZkFold.Base.Protocol.Plonkup.Relation           (PlonkupRelation (..))

data PlonkupProverSetup p i n l f g1 g2 = PlonkupProverSetup
    { omega       :: f
    , k1          :: f
    , k2          :: f
    , gs          :: V.Vector g1
    , sigma1s     :: PolyVec f n
    , sigma2s     :: PolyVec f n
    , sigma3s     :: PolyVec f n
    , relation    :: PlonkupRelation p i n l f
    , polynomials :: PlonkupCircuitPolynomials n f
    }

instance
        ( Show g1
        , Show g2
        , Show f
        , Show (PlonkupRelation p i n l f)
        ) => Show (PlonkupProverSetup p i n l f g1 g2) where
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
