module ZkFold.Symbolic.Cardano.Contracts.ZkLogin
    ( zkLogin
    , Certificate (..)
    , Date
    , ClientId
    , UserToken (..)
    ) where

import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.UInt

data Certificate ctx
    = Certificate
        { kid :: ByteString 320 ctx
        , e   :: UInt 32 'Auto ctx
        , n   :: UInt KeyLength 'Auto ctx
        }

type Date ctx = UInt 64 'Auto ctx

type ClientId ctx = ByteString 256 ctx

data UserToken ctx
    = UserToken
        { validUntil :: Date ctx
        , aud        :: ByteString 256 ctx
        , signature  :: Signature ctx
        }

tokenBits :: Symbolic ctx => UserToken ctx -> ByteString 320 ctx
tokenBits UserToken{..} = from validUntil `append` aud

zkLogin
    :: forall ctx
    .  RSA ctx 320
    => Certificate ctx
    -> UserToken ctx
    -> Date ctx
    -> ClientId ctx
    -> Bool ctx
zkLogin Certificate{..} token@UserToken{..} date clientId = sigValid && dateValid && audValid
    where
        dateValid = validUntil < date
        audValid  = aud == clientId
        sigValid  = verify (tokenBits token) signature (PublicKey e n)
