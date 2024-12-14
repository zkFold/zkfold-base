module Examples.Ed25519 (
    exampleEd25519Scale
  ) where

import           Control.DeepSeq                         (NFData)

import           ZkFold.Base.Algebra.Basic.Class         (Scale (..))
import           ZkFold.Base.Algebra.EllipticCurve.Class (Point)
import           ZkFold.Base.Data.Vector                 (Vector)
import           ZkFold.Symbolic.Class                   (Symbolic)
import           ZkFold.Symbolic.Data.Ed25519            (AcEd25519)
import           ZkFold.Symbolic.Data.FFA                (Size)
import           ZkFold.Symbolic.Data.FieldElement       (FieldElement)

exampleEd25519Scale
    :: Symbolic c
    => NFData (c (Vector Size))
    => FieldElement c
    -> Point (AcEd25519 c)
    -> Point (AcEd25519 c)
exampleEd25519Scale = scale
