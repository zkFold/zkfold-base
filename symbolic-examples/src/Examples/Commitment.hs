{-# LANGUAGE TypeOperators #-}

module Examples.Commitment (
    exampleCommitment
  ) where

import           Control.DeepSeq                           (NFData)

import           ZkFold.Base.Algebra.EllipticCurve.Class   as EC
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Base.Data.Vector                   (Vector)
import           ZkFold.Base.Protocol.Protostar.Commit     (hcommit)
import           ZkFold.Symbolic.Class                     (Symbolic)
import           ZkFold.Symbolic.Data.Ed25519              ()
import           ZkFold.Symbolic.Data.FFA
import           ZkFold.Symbolic.Data.FieldElement

exampleCommitment 
    :: Symbolic c
    => NFData (c (Vector Size))
    => FieldElement c 
    -> FieldElement c 
    -> Point (Ed25519 c)
exampleCommitment = hcommit
