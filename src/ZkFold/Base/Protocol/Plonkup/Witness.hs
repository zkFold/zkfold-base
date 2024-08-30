{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Data.Map.Strict                                     (Map)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                             (Vector)

data PlonkWitnessInput i c = PlonkWitnessInput (Vector i (ScalarField c)) (Map Natural (ScalarField c))

instance Show (ScalarField c) => Show (PlonkWitnessInput i c) where
    show (PlonkWitnessInput v m) = "Witness Input: " ++ show v <> "Witness New Vars: " ++ show m
