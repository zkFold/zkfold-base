-- TODO: Move this module to Symbolic Algorithms (JWT verification is reusable)

module ZkFold.Symbolic.Cardano.Contracts.JWT
    ( Certificate (..)
    , Date (..)
    , TokenHeader (..)
    , TokenPayload (..)
    , Signature
    , ClientSecret (..)
    , secretBits
    , verifySignature
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

data Certificate ctx
    = Certificate
        { kid :: ByteString 320 ctx
        , e   :: UInt 32 'Auto ctx
        , n   :: UInt KeyLength 'Auto ctx
        }

type Date ctx = UInt 64 'Auto ctx

type family ElemAt (lst :: [a]) (ix :: Natural) :: a where
    ElemAt (x ': xs) 0 = x
    ElemAt (x ': xs) n = ElemAt xs (n - 1)

data TokenHeader (lengths :: [Natural]) ctx
    = TokenHeader
        { hdAlg :: ByteString (ElemAt lengths 0) ctx
        -- ^ Signature or encryption algorithm
        , hdKid :: ByteString (ElemAt lengths 1) ctx
        -- ^ Key ID
        , hdTyp :: ByteString (ElemAt lengths 2) ctx
        -- ^ Type of token
        }

data TokenPayload (lengths :: [Natural]) ctx
    = TokenPayload
        { plIss :: ByteString (ElemAt lengths 0) ctx 
        -- ^ Issuer (who created and signed the token)
        , plAzp :: ByteString (ElemAt lengths 1) ctx 
        -- ^ Authorized party (the party to which the token was issued)
        , plAud :: ByteString (ElemAt lengths 2) ctx 
        -- ^ Audience (who or what the token is intended for)
        , plSub :: ByteString (ElemAt lengths 3) ctx 
        -- ^ Subject (whom the token refers to)
        , plHd  :: ByteString (ElemAt lengths 4) ctx
        -- ^  
        , plEmail :: ByteString (ElemAt lengths 5) ctx 
        , plEmail_verified :: ByteString (ElemAt lengths 6) ctx 
        , plAtHash :: ByteString (ElemAt lengths 7) ctx 
        -- ^ Access token hash value
        , plName :: ByteString (ElemAt lengths 8) ctx 
        , plPicture :: ByteString (ElemAt lengths 9) ctx 
        , plGivenName :: ByteString (ElemAt lengths 10) ctx 
        , plFamilyName :: ByteString (ElemAt lengths 11) ctx 
        , plIat :: ByteString (ElemAt lengths 12) ctx 
        -- ^ Issued at (seconds since Unix epoch)
        , plExp :: ByteString (ElemAt lengths 13) ctx 
        -- ^ Expiration time (seconds since Unix epoch)
        }

data ClientSecret hlens plens ctx
    = ClientSecret
        { header :: TokenHeader hlens ctx
        , payload :: TokenPayload plens ctx
        , signature :: Signature ctx
        }

-- | Client secret as a ByteString: @base64UrlEncode(header) + "." + base64UrlEncode(payload)@
--
secretBits :: Symbolic ctx => ClientSecret hlens plens ctx -> ByteString (SecretBase64Bits hlens plens) ctx
secretBits = undefined

-- | Verify that the given JWT was correctly signed with a matching key (i.e. Key IDs match and the signature is correct).
--
verifySignature :: Symbolic ctx => Certificate ctx -> ClientSecret hlens plens ctx -> Bool ctx
verifySignature Certificate{..} secret = kid == hdKid header && verify (secretBits secret) (signature secret) (PublicKey e n)

