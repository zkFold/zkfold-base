module Examples.Commitment (
    exampleCommitment
  ) where

import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Base.Data.Vector                   (Vector)
import           ZkFold.Base.Protocol.IVC.Commit           (HomomorphicCommit (..))

exampleCommitment
    :: HomomorphicCommit (Vector 1 (ScalarField (Ed25519 c))) (Point (Ed25519 c))
    => Vector 1 (ScalarField (Ed25519 c))
    -> Point (Ed25519 c)
exampleCommitment = hcommit
