module Examples.Commitment (
    exampleCommitment
  ) where

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..), Point)
import           ZkFold.Base.Data.Vector                 (Vector)
import           ZkFold.Base.Protocol.Protostar.Commit   (HomomorphicCommit (..))
import           ZkFold.Symbolic.Data.Ed25519            (AcEd25519)

exampleCommitment
    :: HomomorphicCommit (Vector 1 (ScalarField (AcEd25519 c))) (Point (AcEd25519 c))
    => Vector 1 (ScalarField (AcEd25519 c))
    -> Point (AcEd25519 c)
exampleCommitment = hcommit
