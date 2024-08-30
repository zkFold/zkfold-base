{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Proof where

import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Point)

data PlonkProof c = PlonkProof {
        cmA       :: Point c,
        cmB       :: Point c,
        cmC       :: Point c,
        cmZ       :: Point c,
        cmT1      :: Point c,
        cmT2      :: Point c,
        cmT3      :: Point c,
        proof1    :: Point c,
        proof2    :: Point c,
        a_xi      :: ScalarField c,
        b_xi      :: ScalarField c,
        c_xi      :: ScalarField c,
        s1_xi     :: ScalarField c,
        s2_xi     :: ScalarField c,
        z_xi      :: ScalarField c,
        l1_xi_mul :: ScalarField c
    }
instance (Show (ScalarField c), Show (BaseField c), EllipticCurve c) => Show (PlonkProof c) where
    show PlonkProof {..} =
        "Proof: "
        ++ show cmA ++ " "
        ++ show cmB ++ " "
        ++ show cmC ++ " "
        ++ show cmZ ++ " "
        ++ show cmT1 ++ " "
        ++ show cmT2 ++ " "
        ++ show cmT3 ++ " "
        ++ show proof1 ++ " "
        ++ show proof2 ++ " "
        ++ show a_xi ++ " "
        ++ show b_xi ++ " "
        ++ show c_xi ++ " "
        ++ show s1_xi ++ " "
        ++ show s2_xi ++ " "
        ++ show z_xi
        ++ show l1_xi_mul
