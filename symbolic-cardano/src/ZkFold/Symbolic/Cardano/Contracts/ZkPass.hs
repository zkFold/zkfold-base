{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module ZkFold.Symbolic.Cardano.Contracts.ZkPass where
import           Data.Kind                                   (Type)
import           Data.Maybe                                  (Maybe (Just))
import           Data.Traversable                            (Traversable)
import           Data.Type.Equality
import           Data.Type.Ord                               (OrdCond)
import           GHC.Base                                    (Maybe (Nothing), Monad (return), ($))
import           GHC.IO                                      (unsafePerformIO)
import           GHC.TypeLits                                (KnownNat, Log2)
import qualified GHC.TypeNats
import           Prelude                                     hiding (Bool, Eq (..), concat, head, length, splitAt, (!!),
                                                              (&&), (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp, fromZp)
import           ZkFold.Base.Algebra.Basic.Number            (value)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Base, BLS12_381_G1, BLS12_381_G2,
                                                              BLS12_381_GT (BLS12_381_GT), BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (BaseField, ScalarField, gen),
                                                              Point (Inf, Point))
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Data.Vector                     hiding (concat)
import           ZkFold.Symbolic.Algorithms.ECDSA.ECDSA      (ecdsaVerify)
import           ZkFold.Symbolic.Algorithms.Hash.SHA2        (SHA2N, sha2)
import qualified ZkFold.Symbolic.Class                       as S
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString             (ByteString (ByteString), concat, toWords)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators            (Iso (..), KnownRegisterSize, NumberOfRegisters,
                                                              RegisterSize (..), extend)
import           ZkFold.Symbolic.Data.Conditional            (Conditional (..))
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.Data.UInt                   (UInt (UInt), eea)
data ZKPassResult c = ZKPassResult
  { allocatorAddress   :: ByteString 256 c
  , allocatorSignature :: ByteString 520 c
  , publicFields       :: ByteString 1024 c
  , publicFieldsHash   :: ByteString 256 c
  , taskId             :: ByteString 256 c
  , uHash              :: ByteString 256 c
  , validatorAddress   :: ByteString 256 c
  , validatorSignature :: ByteString 520 c
  , publicKey          :: ByteString 256 c
  }

type Hash c = UInt 256 Auto c

-- TODO: change to keccak256
hashFunction :: forall c . (
    SHA2N "SHA512/256" c
    )
    => ByteString 1024 c
    -> ByteString 256 c
hashFunction = sha2 @"SHA512/256"

verifyAllocatorSignature :: forall context . ( Scale (FieldElement context) (Point BLS12_381_G1)
    , SemiEuclidean (Hash context)
    , Log2 (Order (S.BaseField context) GHC.TypeNats.- 1) ~ 255
    , KnownNat (NumberOfRegisters (S.BaseField context) 256 'Auto)
    , SHA2N "SHA512/256" context
    )
    =>ByteString 256 context
    -> ByteString 256 context
    -> ByteString 256 context
    -> ByteString 520 context
    -> Bool context
verifyAllocatorSignature taskId validatorAddress allocatorAddress allocatorSignature = undefined
    where
        params :: ByteString 1024 context
        params = extend (concat $ V.unsafeToVector [taskId, validatorAddress, allocatorAddress] :: ByteString 768 context)

        encodedParams :: ByteString 256 context
        encodedParams = hashFunction params

        (r, s, v) = extractSignature allocatorSignature

        -- TODO: extract point from bytestring
        publicKey :: Point BLS12_381_G1
        publicKey = undefined

        verifyVerdict :: Bool context
        verifyVerdict = ecdsaVerify @BLS12_381_G1 @BLS12_381_Base @BLS12_381_Scalar @context publicKey encodedParams (r, s)

verifyValidatorSignature :: forall context . (
    Scale (FieldElement context) (Point BLS12_381_G1)
    , SemiEuclidean (Hash context)
    , Log2 (Order (S.BaseField context) GHC.TypeNats.- 1) ~ 255
    , KnownNat (NumberOfRegisters (S.BaseField context) 256 'Auto)
    , SHA2N "SHA512/256" context
    )
    => ByteString 256 context
    -> ByteString 256 context
    -> ByteString 256 context
    -> ByteString 256 context
    -> ByteString 520 context -> Bool context
verifyValidatorSignature taskId uHash publicFieldsHash validatorAddress validatorSignature = verifyVerdict
    where
        params :: ByteString 1024 context
        params = concat $ V.unsafeToVector [taskId, uHash, publicFieldsHash, validatorAddress]

        encodedParams :: ByteString 256 context
        encodedParams = hashFunction params

        (r, s, v) = extractSignature validatorSignature

        -- TODO: extract point from bytestring
        publicKey :: Point BLS12_381_G1
        publicKey = undefined

        verifyVerdict :: Bool context
        verifyVerdict = ecdsaVerify @BLS12_381_G1 @BLS12_381_Base @BLS12_381_Scalar @context publicKey encodedParams (r, s)

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
    . ( Eq (Bool context) (Hash context)
    , SHA2N "SHA512/256" context
    , KnownNat (NumberOfRegisters (S.BaseField context) 256 'Auto)
    , Log2 (Order (S.BaseField context) GHC.TypeNats.- 1) ~ 255
    , SemiEuclidean (Hash context)
    , Scale (FieldElement context) (Point BLS12_381_G1)
    ) =>ZKPassResult context -> Bool context
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
        conditionAllocatorSignatureCorrect = verifyAllocatorSignature
            taskId validatorAddress allocatorAddress allocatorSignature

        conditionHashEquality = hashFunction publicFields == publicFieldsHash

        conditionValidatorSignatureCorrect = verifyValidatorSignature
            taskId uHash publicFieldsHash validatorAddress validatorSignature

    in conditionAllocatorSignatureCorrect && conditionHashEquality && conditionValidatorSignatureCorrect


