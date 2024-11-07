module Examples.RSA (exampleRSA) where

import           GHC.TypeLits                                    (KnownNat)

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (Tx, TxOut, batchTransfer)
import           ZkFold.Symbolic.Cardano.Types                   (Bool, ByteString)
import           ZkFold.Symbolic.Class                           (Symbolic (..))
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.UInt

exampleRSA ::
    ( Symbolic c
    , RSA c 256
    )  => ByteString 256 c -> PrivateKey c -> PublicKey c -> Bool c
exampleRSA msg priv pub = verify msg (sign msg priv) pub
