{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Apps.KYC where

import           Data.Aeson
import           Data.Functor                     ((<$>))
import           Data.Maybe                       (fromJust)
import           GHC.Generics                     (Generic)
import           Prelude                          (String, error, fst, snd, ($), (.))

import           ZkFold.Base.Algebra.Basic.Class  (FromConstant (fromConstant))
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Control.HApplicative (HApplicative)
import           ZkFold.Base.Data.Vector          (Vector, splitAt, toVector)
import           ZkFold.Symbolic.Class            (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Bool        (Bool, not, (&&))
import           ZkFold.Symbolic.Data.ByteString  (ByteString, Resize (resize), concat, toWords)
import           ZkFold.Symbolic.Data.Class       (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators (Ceil, GetRegisterSize, Iso (..), KnownRegisterSize,
                                                   NumberOfRegisters)
import           ZkFold.Symbolic.Data.Eq          (Eq ((==)), elem)
import           ZkFold.Symbolic.Data.Input       (SymbolicInput)
import           ZkFold.Symbolic.Data.Ord         (Ord ((>=)))
import           ZkFold.Symbolic.Data.UInt        (OrdWord, UInt)
import           ZkFold.Symbolic.Interpreter      (Interpreter)

type KYCByteString context = ByteString 256 context

{-
>>> type Prime256_1 = 28948022309329048855892746252171976963363056481941560715954676764349967630337
>>> :{
exKYC :: KYCData (Interpreter (Zp Prime256_1))
exKYC = KYCData
  (fromConstant (1000 :: Natural))
  (fromConstant (2000 :: Natural))
  (fromConstant (3000 :: Natural))
  (fromConstant (4000 :: Natural))
:}
>>> encode exKYC
"{\"kycHash\":\"bb8\",\"kycID\":4000,\"kycType\":\"3e8\",\"kycValue\":\"7d0\"}"
-}
data KYCData n k r context = KYCData
    { kycType  :: ByteString k context
    , kycID    :: UInt k r context
    , kycHash  :: UInt k r context
    , kycValue :: ByteString n context
    } deriving Generic

data User r context = User
    { userAge     :: UInt 8 r context
    , userCountry :: ByteString 10 context
    } deriving Generic

instance ( Symbolic context
         , KnownNat n
         , KnownNat k
         , KnownRegisterSize r
         ) => FromJSON (KYCData n k r context)

instance ( Symbolic (Interpreter (Zp p))
         , KnownNat n
         , KnownNat k
         , KnownRegisterSize r
         ) => ToJSON (KYCData n k r (Interpreter (Zp p)))

instance ( HApplicative context
         , KnownNat n
         , KnownNat k
         , KnownRegisterSize r
         , KnownNat (NumberOfRegisters (BaseField context) k r)
         , Symbolic context
         ) => SymbolicData (KYCData n k r context)

instance (
  Symbolic context
  , KnownNat n
  , KnownNat k
  , KnownRegisterSize r
  , KnownNat (NumberOfRegisters (BaseField context) k r)
  ) => SymbolicInput (KYCData n k r context)

isCitizen :: (Symbolic c) => KYCByteString c -> Vector n (KYCByteString c) -> Bool c
isCitizen = elem

kycExample :: forall n k r rsc context . (
  Symbolic context
  , KnownNat n
  , KnownNat rsc
  , KnownRegisterSize r
  , KnownNat (NumberOfRegisters (BaseField context) 8 r)
  , KnownNat (Ceil (GetRegisterSize (BaseField context) 8 r) OrdWord)
  , KnownNat (NumberOfRegisters (BaseField context) k r)
  ) => KYCData n k r context -> UInt k r context -> Bool context
kycExample kycData hash =
  let
    v :: (Vector 8 (ByteString 1 context), Vector 10 (ByteString 1 context))
    v = splitAt @8 @10 $ toWords $ resize $ kycValue kycData

    correctHash :: Bool context
    correctHash = hash == kycHash kycData

    user :: User r context
    user = User (from $ concat $ fst v) (concat $ snd v)

    validAge :: Bool context
    validAge = userAge user >= fromConstant (18 :: Natural)

    validCountry :: Bool context
    validCountry = not $ elem (userCountry user) (restrictedCountries @rsc)

  in correctHash && validAge && validCountry

userA :: forall r context . (
  Symbolic context
  , KnownRegisterSize r
  ) => User r context
userA = User
  (fromConstant (25 :: Natural))
  (fromConstant $ iso3166 "JPN")

iso3166 :: String -> Natural
iso3166 = \case
  "DEU" -> 276
  "FRA" -> 250
  "GBR" -> 826
  "JPN" -> 392
  "USA" -> 840
  _ -> error "Unknown ISO country code"

restrictedCountries :: forall m context . (
  Symbolic context
  , KnownNat m
  ) => Vector m (ByteString 10 context)
restrictedCountries =
  fromJust $ toVector $ fromConstant . iso3166 <$>
  [ "FRA"
  , "DEU"
  ]
