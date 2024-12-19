module Examples.RSA (exampleRSA) where

import           ZkFold.Symbolic.Algorithms.RSA  (PrivateKey, PublicKey, RSA, sign, verify)
import           ZkFold.Symbolic.Cardano.Types   (Bool)
import           ZkFold.Symbolic.Data.ByteString (ByteString)

exampleRSA :: RSA c 256 => ByteString 256 c -> PrivateKey c -> PublicKey c -> Bool c
exampleRSA msg priv pub = verify msg (sign msg priv) pub
