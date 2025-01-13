{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier.Setup where

import           Prelude                                           hiding (Num (..), drop, length, sum, take, (!!), (/),
                                                                    (^))

import           ZkFold.Base.Algebra.Polynomials.Univariate        hiding (qr)
import           ZkFold.Base.Protocol.Plonkup.Relation             (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments (PlonkupCircuitCommitments (..))

data PlonkupVerifierSetup p i n l f g1 g2 = PlonkupVerifierSetup
    { omega       :: f
    , k1          :: f
    , k2          :: f
    , h1          :: g2
    , sigma1s     :: PolyVec f n
    , sigma2s     :: PolyVec f n
    , sigma3s     :: PolyVec f n
    , relation    :: PlonkupRelation p i n l f
    , commitments :: PlonkupCircuitCommitments g1
    }

instance
        ( Show f
        , Show g1
        , Show g2
        , Show (PlonkupRelation p i n l f)
        ) => Show (PlonkupVerifierSetup p i n l f g1 g2) where
    show PlonkupVerifierSetup {..} =
        "Verifier setup: "
        ++ show omega ++ " "
        ++ show k1 ++ " "
        ++ show k2 ++ " "
        ++ show h1 ++ " "
        ++ show sigma1s ++ " "
        ++ show sigma2s ++ " "
        ++ show sigma3s ++ " "
        ++ show relation ++ " "
        ++ show commitments
