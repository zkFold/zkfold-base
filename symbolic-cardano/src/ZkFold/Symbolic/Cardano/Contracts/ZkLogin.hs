module ZkFold.Symbolic.Cardano.Contracts.ZkLogin
    ( zkLogin
    ) where

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.UInt

import ZkFold.Symbolic.Data.JWT (ClientSecret (..), TokenHeader (..), TokenPayload (..), Certificate, verifySignature)

type PublicInput ctx = ByteString 224 ctx

zkLogin
    :: forall ctx
    .  Symbolic ctx
    => ClientSecret ctx
    -> ByteString 64 ctx
    -> ByteString 32 ctx
    -> Certificate ctx
    -> PublicInput ctx
    -> Bool ctx
zkLogin clientSecret@ClientSecret{..} amount recipient certificate pi = tokenValid
    where
        tokenValid = verifySignature certificate clientSecret


