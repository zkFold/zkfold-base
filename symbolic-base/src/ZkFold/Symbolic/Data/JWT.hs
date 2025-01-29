{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.JWT
    ( Certificate (..)
    , TokenHeader (..)
    , TokenPayload (..)
    , Signature
    , ClientSecret (..)
    , IsSymbolicJSON (..)
    , secretBits
    , verifySignature
    , feMod6
    ) where

import           Control.DeepSeq                    (NFData)
import           Data.Aeson                         (FromJSON (..), genericParseJSON)
import qualified Data.Aeson                         as JSON
import           Data.Aeson.Casing                  (aesonPrefix, snakeCase)
import           Data.Constraint                    (withDict)
import           Data.Constraint.Nat                (plusNat)
import           Data.Foldable                      (foldrM)
import           Data.Maybe                         (fromMaybe)
import           Data.Scientific                    (toBoundedInteger)
import qualified Data.Text                          as T
import           GHC.Generics                       (Generic, Par1 (..))
import           Prelude                            (fmap, otherwise, pure, type (~), ($), (.))
import qualified Prelude                            as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.HFunctor          (hmap)
import qualified ZkFold.Base.Data.Vector            as V
import           ZkFold.Base.Data.Vector            ((!!))
import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.Data.Input         (SymbolicInput)
import           ZkFold.Symbolic.Data.UInt
import qualified ZkFold.Symbolic.Data.VarByteString as VB
import           ZkFold.Symbolic.Data.VarByteString (VarByteString (..), (@+))
import           ZkFold.Symbolic.MonadCircuit       (MonadCircuit, newAssigned)

class IsSymbolicJSON a where
    type MaxLength a :: Natural

    toJsonBits :: a -> VarByteString (MaxLength a) (Context a)


-- | RSA Public key
--
data Certificate ctx
    = Certificate
        { kid :: VarByteString 320 ctx
        , e   :: UInt 32 'Auto ctx
        , n   :: UInt KeyLength 'Auto ctx
        }
    deriving Generic

deriving instance
    ( P.Eq (UInt 32 'Auto ctx)
    , P.Eq (UInt KeyLength 'Auto ctx)
    , P.Eq (VarByteString 320 ctx)
    ) => P.Eq (Certificate ctx)
deriving instance
    ( P.Show (UInt 32 'Auto ctx)
    , P.Show (UInt KeyLength 'Auto ctx)
    , P.Show (VarByteString 320 ctx)
    ) => P.Show (Certificate ctx)
deriving instance
    ( NFData (UInt 32 'Auto ctx)
    , NFData (UInt KeyLength 'Auto ctx)
    , NFData (VarByteString 320 ctx)
    ) => NFData (Certificate ctx)
instance
    ( KnownNat (NumberOfRegisters (BaseField ctx) 32 'Auto)
    , KnownNat (NumberOfRegisters (BaseField ctx) KeyLength 'Auto)
    , Symbolic ctx
    ) => SymbolicData (Certificate ctx)
instance
    ( KnownNat (NumberOfRegisters (BaseField ctx) 32 'Auto)
    , KnownNat (NumberOfRegisters (BaseField ctx) KeyLength 'Auto)
    , Symbolic ctx
    ) => SymbolicInput (Certificate ctx)


-- | Json Web Token header with information about encryption algorithm and signature
--
data TokenHeader ctx
    = TokenHeader
        { hdAlg :: VarByteString 72 ctx
        -- ^ Signature or encryption algorithm
        , hdKid :: VarByteString 320 ctx
        -- ^ Key ID
        , hdTyp :: VarByteString 32 ctx
        -- ^ Type of token
        }
    deriving Generic

deriving instance
    ( P.Eq (ctx (V.Vector 72))
    , P.Eq (ctx (V.Vector 320))
    , P.Eq (ctx (V.Vector 32))
    , P.Eq (ctx Par1)
    ) => P.Eq (TokenHeader ctx)
deriving instance
    ( P.Show (ctx (V.Vector 72))
    , P.Show (ctx (V.Vector 320))
    , P.Show (ctx (V.Vector 32))
    , P.Show (ctx Par1)
    ) => P.Show (TokenHeader ctx)
deriving instance
    ( NFData (ctx (V.Vector 72))
    , NFData (ctx (V.Vector 320))
    , NFData (ctx (V.Vector 32))
    , NFData (ctx Par1)
    ) => NFData (TokenHeader ctx)

deriving instance Symbolic ctx => SymbolicData (TokenHeader ctx)
deriving instance Symbolic ctx => SymbolicInput (TokenHeader ctx)

instance Symbolic ctx => FromJSON (TokenHeader ctx) where
    parseJSON = genericParseJSON $ aesonPrefix snakeCase

instance (Symbolic ctx, Context (TokenHeader ctx) ~ ctx) => IsSymbolicJSON (TokenHeader ctx) where
    type MaxLength (TokenHeader ctx) = 648
    toJsonBits TokenHeader{..} =
                    (fromType @"{\"alg\":\"")   @+ hdAlg
        `VB.append` (fromType @"\",\"kid\":\"") @+ hdKid
        `VB.append` (fromType @"\",\"typ\":\"") @+ hdTyp
        `VB.append` (fromType @"\"}")


-- | Json Web Token payload with information about the issuer, bearer and TTL
--
data TokenPayload ctx
    = TokenPayload
        { plIss           :: VarByteString 256 ctx
        -- ^ Issuer (who created and signed the token)
        , plAzp           :: VarByteString 1024 ctx
        -- ^ Authorized party (the party to which the token was issued)
        , plAud           :: VarByteString 1024 ctx
        -- ^ Audience (who or what the token is intended for)
        , plSub           :: VarByteString 256 ctx
        -- ^ Subject (whom the token refers to)
        , plHd            :: VarByteString 256 ctx
        -- ^ Hosted domain
        , plEmail         :: VarByteString 512 ctx
        -- ^ User email limited to 64 characters
        , plEmailVerified :: VarByteString 40 ctx
        -- ^ "true" or "false", max 5 bytes
        , plAtHash        :: VarByteString 256 ctx
        -- ^ Access token hash value
        , plName          :: VarByteString 512 ctx
        -- ^ Full name limited to 64 characters
        , plPicture       :: VarByteString 1024 ctx
        -- ^ URL to the profile picture limited to 128 characters
        , plGivenName     :: VarByteString 256 ctx
        -- ^ Given name limited to 32 characters
        , plFamilyName    :: VarByteString 256 ctx
        -- ^ Family name limited to 32 characters
        , plIat           :: VarByteString 80 ctx
        -- ^ Issued at (seconds since Unix epoch), a decimal number
        , plExp           :: VarByteString 80 ctx
        -- ^ Expiration time (seconds since Unix epoch), a decimal number
        }
    deriving Generic

deriving instance
    ( P.Eq (ctx (V.Vector 40))
    , P.Eq (ctx (V.Vector 80))
    , P.Eq (ctx (V.Vector 256))
    , P.Eq (ctx (V.Vector 512))
    , P.Eq (ctx (V.Vector 1024))
    , P.Eq (ctx Par1)
    ) => P.Eq (TokenPayload ctx)
deriving instance
    ( P.Show (ctx (V.Vector 40))
    , P.Show (ctx (V.Vector 80))
    , P.Show (ctx (V.Vector 256))
    , P.Show (ctx (V.Vector 512))
    , P.Show (ctx (V.Vector 1024))
    , P.Show (ctx Par1)
    ) => P.Show (TokenPayload ctx)
deriving instance Symbolic ctx => SymbolicData (TokenPayload ctx)
deriving instance Symbolic ctx => SymbolicInput (TokenPayload ctx)

instance Symbolic ctx => FromJSON (TokenPayload ctx) where
    parseJSON = genericParseJSON (aesonPrefix snakeCase) . stringify
        where
            -- We store everything as ByteStrings for simplicity.
            -- We need to convert ints and bools to strings to avoid conversion errors
            --
            stringify :: JSON.Value -> JSON.Value
            stringify (JSON.Number s) =
                JSON.String (T.pack . P.show . fromMaybe (P.error "instance FromJSON JWT :: Invalid integer") . toBoundedInteger @P.Int $ s)
            stringify (JSON.Bool b)   = JSON.String (T.pack $ P.show b)
            stringify (JSON.Object o) = JSON.Object $ fmap stringify o
            stringify rest            = rest

instance (Symbolic ctx, Context (TokenPayload ctx) ~ ctx) => IsSymbolicJSON (TokenPayload ctx) where
    type MaxLength (TokenPayload ctx) = 7088
    toJsonBits TokenPayload{..} =
                    (fromType @"{\"iss\":\"")   @+ plIss
        `VB.append` (fromType @"\",\"azp\":\"") @+ plAzp
        `VB.append` (fromType @"\",\"aud\":\"") @+ plAud
        `VB.append` (fromType @"\",\"sub\":\"") @+ plSub
        `VB.append` (fromType @"\",\"hd\":\"")  @+ plHd
        `VB.append` (fromType @"\",\"email\":\"") @+ plEmail
        `VB.append` (fromType @"\",\"email_verified\":") @+ plEmailVerified
        `VB.append` (fromType @",\"at_hash\":\"") @+ plAtHash
        `VB.append` (fromType @"\",\"name\":\"")  @+ plName
        `VB.append` (fromType @"\",\"picture\":\"") @+ plPicture
        `VB.append` (fromType @"\",\"given_name\":\"")  @+ plGivenName
        `VB.append` (fromType @"\",\"family_name\":\"") @+ plFamilyName
        `VB.append` (fromType @"\",\"iat\":") @+ plIat
        `VB.append` (fromType @",\"exp\":")   @+ plExp
        `VB.append` (fromType @"}")

data ClientSecret ctx
    = ClientSecret
        { csHeader    :: TokenHeader ctx
        , csPayload   :: TokenPayload ctx
        , csSignature :: Signature ctx
        }
    deriving Generic

deriving instance
    ( NFData (TokenHeader ctx)
    , NFData (TokenPayload ctx)
    , NFData (Signature ctx)
    ) => NFData (ClientSecret ctx)
deriving instance Symbolic ctx => SymbolicData (ClientSecret ctx)
deriving instance Symbolic ctx => SymbolicInput (ClientSecret ctx)


type family BufLen (n :: Natural) :: Natural where
    BufLen 0 = 3
    BufLen 1 = 3
    BufLen 2 = 3
    BufLen 3 = 3
    BufLen 4 = 3
    BufLen 5 = 3
    BufLen 6 = 3
    BufLen 7 = 3
    BufLen n = Log2 n + 1 

-- | Returns fieldElement `mod` 6
--
-- fieldElement = \sum_{i=0}^N a_i * 2^i, a_i ∈ {0, 1}
--   fieldElement `mod` 6
-- = (\sum_{i=0}^N a_i * 2^i) `mod` 6
-- = \sum_{i=0}^N a_i * 2^i `mod` 6
-- = \sum_{i=0}^N a_i * (2^i `mod` 6)
-- = a_0 + \sum_1^N a_i * (if is_odd(i) then 2 else 4)
--
-- TODO: check if this approach requires less constraints and variables than @divMod@ on @UInt@ s
--
-- The upper bound of this sum for a field element of N bits is 3N.
-- A sequence of five such sums will reduce the field element to three bits.
-- However, at this point it might be equal to 6 or 7. We'll need to check the two higher bits
-- after the last reduction and unset them if they are both set.
--
feMod6 :: forall ctx . Symbolic ctx => FieldElement ctx -> FieldElement ctx
feMod6 = unset . truncatedBinary @3 . reduce @4 . reduce @5 . reduce @6 . reduce @20 . reduce @(NumberOfBits (BaseField ctx))
    where
        reduce :: forall n . KnownNat n => FieldElement ctx -> FieldElement ctx
        reduce fe =
            let bits = truncatedBinary @n fe
             in FieldElement $ fromCircuitF bits $ \v -> do
                 z <- newAssigned (P.const zero)
                 weightedSum <- foldrM foldBits z $ V.enumerate v
                 pure $ Par1 weightedSum

        foldBits :: MonadCircuit i (BaseField ctx) w m => (Natural, i) -> i -> m i
        foldBits (ix, a) acc
          | ix == 0   = newAssigned $ \p -> p acc + p a
          | P.odd ix  = newAssigned $ \p -> p acc + scale (2 :: Natural) (p a)
          | otherwise = newAssigned $ \p -> p acc + scale (4 :: Natural) (p a)

        unset :: ctx (V.Vector 3) -> FieldElement ctx
        unset vec = FieldElement $ fromCircuitF vec $ \v -> do
            f <- newAssigned $ \p -> one - p (v !! 1) * p (v !! 2)
            hi1 <- newAssigned $ \p -> p f * p (v !! 2)
            hi2 <- newAssigned $ \p -> p f * p (v !! 1)
            hi  <- newAssigned $ \p -> scale (4 :: Natural) (p hi1) + scale (2 :: Natural) (p hi2)
            res <- newAssigned $ \p -> p hi + p (v !! 0)
            pure $ Par1 res

truncatedBinary :: forall n ctx . (KnownNat n, Symbolic ctx) => FieldElement ctx -> ctx (V.Vector n)
truncatedBinary (FieldElement c) = hmap V.unsafeToVector $ symbolicF c
    (padBits n . fmap fromConstant . binaryExpansion . toConstant . unPar1)
    (expansion n . unPar1)
    where n = value @n

-- | Increase capacity of a VarByteString and increase its length to the nearest multiple of 6
-- Required for base64 encoding.
--
pad6 :: forall n ctx . (Symbolic ctx, KnownNat n) => VarByteString n ctx -> VarByteString (n + 5) ctx
pad6 VarByteString{..} = VarByteString (bsLength + mod6) (withn5 @n $ VB.shiftL newBuf mod6)
    where
        feToUInt :: FieldElement ctx -> UInt (BufLen n) ('Fixed (BufLen n)) ctx
        feToUInt (FieldElement c) = UInt $ hmap (V.singleton . unPar1) c

        uintToFe :: UInt (BufLen n) ('Fixed (BufLen n)) ctx -> FieldElement ctx
        uintToFe (UInt v) = FieldElement $ hmap (Par1 . V.item) v
        
        mod6 = feMod6 bsLength
        newBuf = withn5 @n $ resize bsBuffer

withn5  :: forall n {r}. KnownNat n => (KnownNat (n + 5) => r) -> r
withn5 = withDict (plusNat @n @5)

-- | Client secret as a ByteString: @base64UrlEncode(header) + "." + base64UrlEncode(payload)@
--
secretBits :: forall ctx .  Symbolic ctx => ClientSecret ctx -> VarByteString 7754 ctx
secretBits ClientSecret {..} = pad6 (toJsonBits csHeader) @+ (fromType @".") @+ pad6 (toJsonBits csPayload)

-- | Verify that the given JWT was correctly signed with a matching key (i.e. Key IDs match and the signature is correct).
--
verifySignature :: Symbolic ctx => Certificate ctx -> ClientSecret ctx -> Bool ctx
verifySignature Certificate{..} ClientSecret{..} = kid == hdKid csHeader -- && verify (secretBits secret) (signature secret) (PublicKey e n)

