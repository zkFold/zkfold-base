{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.RecursiveFunction where

import           GHC.Generics                               (Generic)

import           ZkFold.Base.Algebra.Basic.Number           (type (-))
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (StepFunction)

-- | Public input for the recursive function
data RecursiveI k i c f = RecursiveI (i f) (AccumulatorInstance k i c f)
    deriving (GHC.Generics.Generic)

deriving instance (HashAlgorithm algo f, RandomOracle algo (i f) f, RandomOracle algo c f) => RandomOracle algo (RecursiveI k i c f) f

-- | Payload for the recursive function
data RecursiveP d k i p c f = RecursiveP (i f) (p f) f (AccumulatorInstance k i c f) (Vector k c) (Vector (d-1) c)
    deriving (GHC.Generics.Generic)

-- TODO: Implement the recursive function.
recursiveFunction :: StepFunction nx nu -> StepFunction nx nu
recursiveFunction f = f
