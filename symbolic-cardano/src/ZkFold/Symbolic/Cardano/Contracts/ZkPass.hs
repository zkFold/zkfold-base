{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module ZkFold.Symbolic.Cardano.Contracts.ZkPass where
import           Data.Kind                                   (Type)
import           Data.Type.Equality
import           GHC.TypeLits                                (KnownNat, Log2)
import qualified GHC.TypeNats
import           Prelude                                     hiding (Bool, Eq (..), concat, head, length, splitAt, (!!),
                                                              (&&), (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Base, BLS12_381_G1, BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (BaseField), Point)
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Data.Vector                     hiding (concat)
import           ZkFold.Symbolic.Algorithms.Hash.SHA2        (SHA2N, sha2)
import qualified ZkFold.Symbolic.Class                       as S
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString             (ByteString, concat, toWords)
import           ZkFold.Symbolic.Data.Combinators            (Iso (..), NumberOfRegisters, RegisterSize (..), extend)
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.Data.UInt                   (UInt)
data ZKPassResult curve c = ZKPassResult
  { allocatorAddress   :: ByteString 256 c
  , allocatorSignature :: ByteString 520 c
  , publicFields       :: ByteString 1024 c
  , publicFieldsHash   :: ByteString 256 c
  , taskId             :: ByteString 256 c
  , uHash              :: ByteString 256 c
  , validatorAddress   :: ByteString 256 c
  , validatorSignature :: ByteString 520 c
  , publicKey          :: Point curve
  }

type Hash c = UInt 256 Auto c

-- TODO: change to keccak256
hashFunction :: forall c . (
    SHA2N "SHA512/256" c
    )
    => ByteString 1024 c
    -> ByteString 256 c
hashFunction = sha2 @"SHA512/256"

verifyAllocatorSignature :: forall curve context p1 p2 . (
    EllipticCurve curve
    , BaseField curve ~ Zp p1
    , KnownNat p2
    , Scale (FieldElement context) (Point curve)
    , SemiEuclidean (Hash context)
    , Log2 (Order (S.BaseField context) GHC.TypeNats.- 1) ~ 255
    , KnownNat (NumberOfRegisters (S.BaseField context) 256 'Auto)
    , SHA2N "SHA512/256" context
    )
    => ByteString 256 context
    -> ByteString 256 context
    -> ByteString 256 context
    -> ByteString 520 context
    -> Point curve
    -> Bool context
verifyAllocatorSignature taskId validatorAddress allocatorAddress allocatorSignature publicKey = verifyVerdict
    where
        params :: ByteString 1024 context
        params = extend (concat $ V.unsafeToVector [taskId, validatorAddress, allocatorAddress] :: ByteString 768 context)

        encodedParams :: ByteString 256 context
        encodedParams = hashFunction params

        (r, s, v) = extractSignature allocatorSignature

        verifyVerdict :: Bool context
        verifyVerdict = ecdsaVerify @curve @p1 @p2 @context publicKey encodedParams (r, s)

verifyValidatorSignature :: forall curve context p1 p2 . (
    EllipticCurve curve
    , BaseField curve ~ Zp p1
    , KnownNat p2
    , Scale (FieldElement context) (Point curve)
    , SemiEuclidean (Hash context)
    , Log2 (Order (S.BaseField context) GHC.TypeNats.- 1) ~ 255
    , KnownNat (NumberOfRegisters (S.BaseField context) 256 'Auto)
    , SHA2N "SHA512/256" context
    )
    => ByteString 256 context
    -> ByteString 256 context
    -> ByteString 256 context
    -> ByteString 256 context
    -> ByteString 520 context
    -> Point curve
    -> Bool context
verifyValidatorSignature taskId uHash publicFieldsHash validatorAddress validatorSignature publicKey = verifyVerdict
    where
        params :: ByteString 1024 context
        params = concat $ V.unsafeToVector [taskId, uHash, publicFieldsHash, validatorAddress]

        encodedParams :: ByteString 256 context
        encodedParams = hashFunction params

        (r, s, v) = extractSignature validatorSignature

        verifyVerdict :: Bool context
        verifyVerdict = ecdsaVerify @curve @p1 @p2 @context publicKey encodedParams (r, s)

extractSignature :: forall context . (Symbolic context)
    => ByteString 520 context
    -> (Hash context,  Hash context, ByteString 8 context)
extractSignature sign = (from $ concat r', from $ concat s', item v')
    where
        r' :: Vector 32 (ByteString 8 context)

        bytes = toWords sign

        (r', l') = splitAt bytes

        (s', v') = splitAt l'

zkPassSymbolicVerifier ::
    forall (context :: (Type -> Type) -> Type)
    . ( SHA2N "SHA512/256" context
    , KnownNat (NumberOfRegisters (S.BaseField context) 256 'Auto)
    , Log2 (Order (S.BaseField context) GHC.TypeNats.- 1) ~ 255
    , SemiEuclidean (Hash context)
    , Scale (FieldElement context) (Point BLS12_381_G1)
    )
    =>ZKPassResult BLS12_381_G1 context
    -> Bool context
zkPassSymbolicVerifier (ZKPassResult
    allocatorAddress
    allocatorSignature
    publicFields
    publicFieldsHash
    taskId
    uHash
    validatorAddress
    validatorSignature
    publicKey
   ) =
    let
        conditionAllocatorSignatureCorrect = verifyAllocatorSignature @BLS12_381_G1 @context @BLS12_381_Base @BLS12_381_Scalar
            taskId validatorAddress allocatorAddress allocatorSignature publicKey

        conditionHashEquality = hashFunction publicFields == publicFieldsHash

        conditionValidatorSignatureCorrect = verifyValidatorSignature @BLS12_381_G1 @context @BLS12_381_Base @BLS12_381_Scalar
            taskId uHash publicFieldsHash validatorAddress validatorSignature publicKey

    in conditionAllocatorSignatureCorrect && conditionHashEquality && conditionValidatorSignatureCorrect


