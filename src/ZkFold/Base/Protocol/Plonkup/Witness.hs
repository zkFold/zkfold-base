{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Data.Map.Strict                         (Map)
import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                 (Vector)

data PlonkupWitnessInput i c = PlonkupWitnessInput (Vector i (ScalarField c)) (Map Natural (ScalarField c))

instance Show (ScalarField c) => Show (PlonkupWitnessInput i c) where
    show (PlonkupWitnessInput v m) = "Plonkup Witness Input: " ++ show v <> "Plonkup Witness New Vars: " ++ show m
