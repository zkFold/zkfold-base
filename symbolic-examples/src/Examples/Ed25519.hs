{-# LANGUAGE TypeOperators #-}

module Examples.Ed25519 (
    exampleEd25519Scale
  ) where

import           Control.DeepSeq                           (NFData)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Symbolic.Data.Ed25519
import           ZkFold.Base.Data.Vector                   (Vector)
import           ZkFold.Symbolic.Class                     (Symbolic)
import           ZkFold.Symbolic.Data.Ed25519              ()
import           ZkFold.Symbolic.Data.FFA
import           ZkFold.Symbolic.Data.FieldElement

exampleEd25519Scale
    :: Symbolic c
    => NFData (c (Vector Size))
    => FieldElement c
    -> Point (AcEd25519 c)
    -> Point (AcEd25519 c)
exampleEd25519Scale = scale
