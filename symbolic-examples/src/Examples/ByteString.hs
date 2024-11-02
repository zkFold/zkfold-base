{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Examples.ByteString (
    exampleByteStringAnd,
    exampleByteStringOr,
    exampleByteStringExtend,
    exampleByteStringAdd,
    exampleSHA,
    exampleByteStringXor,
    exampleByteStringRotate5,
    exampleByteStringIso
  ) where

import           GHC.TypeNats

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.SHA2
import           ZkFold.Symbolic.Class                (Symbolic)
import           ZkFold.Symbolic.Data.Bool            (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString      (ByteString, ShiftBits (rotateBits))
import           ZkFold.Symbolic.Data.Combinators     (Extend (..), Iso (..), RegisterSize (..), KnownRegisterSize)
import           ZkFold.Symbolic.Data.UInt            (UInt)

exampleByteStringAnd ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAnd = (&&)

exampleByteStringOr ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringOr = (||)

exampleByteStringXor ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringXor = xor

exampleByteStringExtend ::
  (KnownNat n, KnownNat k, n <= k, Symbolic c) =>
  ByteString n c -> ByteString k c
exampleByteStringExtend = extend

exampleByteStringRotate5 ::
  (KnownNat n, Symbolic c) =>
  ByteString n c -> ByteString n c
exampleByteStringRotate5 s = rotateBits s 5

exampleByteStringAdd ::
  forall n c. (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAdd x y = from (from x + from y :: UInt n Auto c)

exampleByteStringIso ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  ByteString n c -> UInt n r c
exampleByteStringIso = from

exampleSHA :: forall n c.
  SHA2 "SHA256" c n
  => ByteString n c -> ByteString 256 c
exampleSHA = sha2 @"SHA256"
