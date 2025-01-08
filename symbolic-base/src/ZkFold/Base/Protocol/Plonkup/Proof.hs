{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Proof where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class (Point)

data PlonkupProof baseField scalarField = PlonkupProof {
        cmA     :: Point Bool baseField,
        cmB     :: Point Bool baseField,
        cmC     :: Point Bool baseField,
        cmF     :: Point Bool baseField,
        cmH1    :: Point Bool baseField,
        cmH2    :: Point Bool baseField,
        cmZ1    :: Point Bool baseField,
        cmZ2    :: Point Bool baseField,
        cmQlow  :: Point Bool baseField,
        cmQmid  :: Point Bool baseField,
        cmQhigh :: Point Bool baseField,
        proof1  :: Point Bool baseField,
        proof2  :: Point Bool baseField,
        a_xi    :: scalarField,
        b_xi    :: scalarField,
        c_xi    :: scalarField,
        s1_xi   :: scalarField,
        s2_xi   :: scalarField,
        f_xi    :: scalarField,
        t_xi    :: scalarField,
        t_xi'   :: scalarField,
        z1_xi'  :: scalarField,
        z2_xi'  :: scalarField,
        h1_xi'  :: scalarField,
        h2_xi   :: scalarField,
        l1_xi   :: scalarField
        -- ^ The denominator in the L_1 polynomial evaluation
    }
instance (Show scalarField, Show baseField)
  => Show (PlonkupProof baseField scalarField) where
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
