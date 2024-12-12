{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.RecursiveFunction where

import           GHC.Generics                          (Generic)

import           ZkFold.Base.Algebra.Basic.Number      (type (-))
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator  hiding (pi)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate    (StepFunction)
import GHC.Base (undefined)

-- | Public input to the recursive function
data RecursiveI k i c f = RecursiveI (i f) (AccumulatorInstance k i c f)
    deriving (GHC.Generics.Generic)

deriving instance (HashAlgorithm algo f, RandomOracle algo (i f) f, RandomOracle algo (c f) f) => RandomOracle algo (RecursiveI k i c f) f

-- | Payload to the recursive function
data RecursiveP d k i p c f = RecursiveP (p f) f (Vector k (c f)) (Vector (d-1) (c f))
    deriving (GHC.Generics.Generic)

-- TODO: Implement the recursive function.
recursiveFunction :: forall d k a i p c . StepFunction a i p -> StepFunction a (RecursiveI k i c) (RecursiveP d k i p c)
recursiveFunction func =
    let
        funcRecursive :: StepFunction a (RecursiveI k i c) (RecursiveP d k i p c)
        funcRecursive (RecursiveI x accX) (RecursiveP u flag piX pf) =
            let
                x' = func x u
            in
                -- RecursiveP i' p f acc' cs e
                undefined

    in funcRecursive
