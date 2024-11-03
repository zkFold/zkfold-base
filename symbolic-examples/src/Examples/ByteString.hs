{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

module Examples.ByteString (
    exampleByteStringAnd,
    exampleByteStringOr,
    exampleByteStringResize,
    exampleByteStringAdd,
    exampleSHA,
    exampleByteStringTruncate
  ) where

import           GHC.TypeNats

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.SHA2
import           ZkFold.Symbolic.Class                (Symbolic)
import           ZkFold.Symbolic.Data.Bool            (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString      (ByteString, truncate)
import           ZkFold.Symbolic.Data.Combinators     (Resize (..), Iso (..), RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt            (UInt)

exampleByteStringAnd ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAnd = (&&)

exampleByteStringOr ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringOr = (||)

exampleByteStringResize ::
  (KnownNat n, KnownNat k, Symbolic c) =>
  ByteString n c -> ByteString k c
exampleByteStringResize = resize

exampleByteStringAdd ::
  forall n c. (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAdd x y = from (from x + from y :: UInt n Auto c)

exampleSHA :: forall n c.
  SHA2 "SHA256" c n
  => ByteString n c -> ByteString 256 c
exampleSHA = sha2 @"SHA256"

exampleByteStringTruncate :: forall n k c.
  (KnownNat k, Symbolic c, k <= n) =>
  ByteString n c -> ByteString k c
exampleByteStringTruncate = truncate