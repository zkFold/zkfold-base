{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Proof where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..), Point)

data PlonkupProof c = PlonkupProof {
        cmA     :: Point c,
        cmB     :: Point c,
        cmC     :: Point c,
        cmF     :: Point c,
        cmH1    :: Point c,
        cmH2    :: Point c,
        cmZ1    :: Point c,
        cmZ2    :: Point c,
        cmQlow  :: Point c,
        cmQmid  :: Point c,
        cmQhigh :: Point c,
        proof1  :: Point c,
        proof2  :: Point c,
        a_xi    :: ScalarField c,
        b_xi    :: ScalarField c,
        c_xi    :: ScalarField c,
        s1_xi   :: ScalarField c,
        s2_xi   :: ScalarField c,
        f_xi    :: ScalarField c,
        t_xi    :: ScalarField c,
        t_xi'   :: ScalarField c,
        z1_xi'  :: ScalarField c,
        z2_xi'  :: ScalarField c,
        h1_xi'  :: ScalarField c,
        h2_xi   :: ScalarField c,
        l1_xi   :: ScalarField c
        -- ^ The denominator of the Lagrange polynomial evaluation
    }
instance (Show (ScalarField c), Show (BaseField c), EllipticCurve c) => Show (PlonkupProof c) where
    show PlonkupProof {..} =
        "Plonkup Proof: "
        ++ show cmA ++ " "
        ++ show cmB ++ " "
        ++ show cmC ++ " "
        ++ show cmF ++ " "
        ++ show cmH1 ++ " "
        ++ show cmH2 ++ " "
        ++ show cmZ1 ++ " "
        ++ show cmZ2 ++ " "
        ++ show cmQlow ++ " "
        ++ show cmQmid ++ " "
        ++ show cmQhigh ++ " "
        ++ show proof1 ++ " "
        ++ show proof2 ++ " "
        ++ show a_xi ++ " "
        ++ show b_xi ++ " "
        ++ show c_xi ++ " "
        ++ show s1_xi ++ " "
        ++ show s2_xi ++ " "
        ++ show f_xi ++ " "
        ++ show t_xi ++ " "
        ++ show t_xi' ++ " "
        ++ show z1_xi' ++ " "
        ++ show z2_xi' ++ " "
        ++ show h1_xi' ++ " "
        ++ show h2_xi ++ " "
        ++ show l1_xi
