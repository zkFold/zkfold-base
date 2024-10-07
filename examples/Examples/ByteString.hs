{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Examples.ByteString (
    exampleByteStringAnd,
    exampleByteStringOr,
    exampleByteStringExtend,
    exampleByteStringAdd,
    exampleSHA
  ) where

import           Data.Type.Equality               (type (~))
import           GHC.TypeNats

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.SHA2
import           ZkFold.Symbolic.Class                (Symbolic)
import           ZkFold.Symbolic.Data.Bool            (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString      (ByteString)
import           ZkFold.Symbolic.Data.Combinators     (Extend (..), Iso (..), RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt            (UInt)

exampleByteStringAnd ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAnd = (&&)

exampleByteStringOr ::
  (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringOr = (||)

exampleByteStringExtend ::
  (KnownNat n, KnownNat k, n <= k, Symbolic c) =>
  ByteString n c -> ByteString k c
exampleByteStringExtend = extend

exampleByteStringAdd ::
  forall n c. (KnownNat n, Symbolic c) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAdd x y = from (from x + from y :: UInt n Auto c)

exampleSHA :: forall n c.
  SHA2 "SHA256" c n
  => Div (PaddedLength n 512 64) 512 * 512 ~ PaddedLength n 512 64
  => n <= PaddedLength n 512 64
  => ByteString n c -> ByteString 256 c
exampleSHA = sha2 @"SHA256"
