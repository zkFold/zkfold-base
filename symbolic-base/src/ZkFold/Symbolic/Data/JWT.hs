{-# LANGUAGE OverloadedStrings #-}

module ZkFold.Symbolic.Data.JWT
    ( Certificate (..)
    , TokenHeader (..)
    , TokenPayload (..)
    , Signature
    , ClientSecret (..)
    , secretBits
    , headerBase64Bits
    , verifySignature
    ) where

import           Data.Aeson                         (FromJSON (..), genericParseJSON)
import           Data.Aeson.Casing                  (aesonPrefix, snakeCase)
import           GHC.Generics                       (Generic)
import           Prelude                            (($))
import qualified Prelude                            as P

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.UInt
import qualified ZkFold.Symbolic.Data.VarByteString as VB
import           ZkFold.Symbolic.Data.VarByteString (VarByteString)

class IsSymbolicJSON a where
    type MaxLength a :: Natural

    toJsonBits :: a -> VarByteString (MaxLength a) (Context a)



data Certificate ctx
    = Certificate
        { kid :: VarByteString 320 ctx
        , e   :: UInt 32 'Auto ctx
        , n   :: UInt KeyLength 'Auto ctx
        }
    deriving Generic

data TokenHeader ctx
    = TokenHeader
        { hdAlg :: VarByteString 64 ctx
        -- ^ Signature or encryption algorithm
        , hdKid :: VarByteString 320 ctx
        -- ^ Key ID
        , hdTyp :: VarByteString 32 ctx
        -- ^ Type of token
        }
    deriving Generic

instance Symbolic ctx => FromJSON (TokenHeader ctx) where
   parseJSON = genericParseJSON $ aesonPrefix snakeCase

data TokenPayload ctx
    = TokenPayload
        { plIss            :: VarByteString 256 ctx
        -- ^ Issuer (who created and signed the token)
        , plAzp            :: VarByteString 1024 ctx
        -- ^ Authorized party (the party to which the token was issued)
        , plAud            :: VarByteString 1024 ctx
        -- ^ Audience (who or what the token is intended for)
        , plSub            :: VarByteString 256 ctx
        -- ^ Subject (whom the token refers to)
        , plHd             :: VarByteString 256 ctx
        -- ^ Hosted domain
        , plEmail          :: VarByteString 512 ctx
        -- ^ User email limited to 64 characters
        , plEmail_verified :: VarByteString 40 ctx
        -- ^ "true" or "false", max 5 bytes
        , plAtHash         :: VarByteString 256 ctx
        -- ^ Access token hash value
        , plName           :: VarByteString 512 ctx
        -- ^ Full name limited to 64 characters
        , plPicture        :: VarByteString 1024 ctx
        -- ^ URL to the profile picture limited to 128 characters
        , plGivenName      :: VarByteString 256 ctx
        -- ^ Given name limited to 32 characters
        , plFamilyName     :: VarByteString 256 ctx
        -- ^ Family name limited to 32 characters
        , plIat            :: VarByteString 80 ctx
        -- ^ Issued at (seconds since Unix epoch), a decimal number
        , plExp            :: VarByteString 80 ctx
        -- ^ Expiration time (seconds since Unix epoch), a decimal number
        }
    deriving Generic

instance Symbolic ctx => FromJSON (TokenPayload ctx) where
   parseJSON = genericParseJSON $ aesonPrefix snakeCase


data ClientSecret ctx
    = ClientSecret
        { header    :: TokenHeader ctx
        , payload   :: TokenPayload ctx
        , signature :: Signature ctx
        }
    deriving Generic

headerBase64Bits :: forall ctx . Symbolic ctx => TokenHeader ctx -> VarByteString 640 ctx
headerBase64Bits TokenHeader{..} =
             ("{\"alg\":\"" :: VarByteString 64 ctx)
    `VB.append` hdAlg
    `VB.append` ("\",\"kid\":\"" :: VarByteString 72 ctx)
    `VB.append` hdKid
    `VB.append` ("\",\"typ\":\"" :: VarByteString 72 ctx)
    `VB.append` hdTyp
    `VB.append` ("\"}" :: VarByteString 16 ctx)

-- | Client secret as a ByteString: @base64UrlEncode(header) + "." + base64UrlEncode(payload)@
--
secretBits :: Symbolic ctx => ClientSecret ctx -> VarByteString 12 ctx
secretBits = P.undefined

-- | Verify that the given JWT was correctly signed with a matching key (i.e. Key IDs match and the signature is correct).
--
verifySignature :: Symbolic ctx => Certificate ctx -> ClientSecret ctx -> Bool ctx
verifySignature = P.undefined
--verifySignature Certificate{..} secret = kid == hdKid header && verify (secretBits secret) (signature secret) (PublicKey e n)

