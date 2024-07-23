{-# LANGUAGE TypeOperators #-}

module Examples.ByteString (
    exampleByteStringAnd,
    exampleByteStringOr,
    exampleByteStringExtend,
    exampleByteStringAdd,
    exampleSHA
  ) where

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number     (KnownNat, type (<=))
import           ZkFold.Symbolic.Algorithms.Hash.SHA2 (SHA2, sha2)
import           ZkFold.Symbolic.Class                (Symbolic)
import           ZkFold.Symbolic.Data.Bool            (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString      (ByteString)
import           ZkFold.Symbolic.Data.Combinators     (Extend (..), Iso (..), RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt            (UInt)

exampleByteStringAnd ::
  (Symbolic c, KnownNat n) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAnd = (&&)

exampleByteStringOr ::
  (Symbolic c, KnownNat n) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringOr = (||)

exampleByteStringExtend ::
  (Symbolic c, KnownNat n, KnownNat k, n <= k) =>
  ByteString n c -> ByteString k c
exampleByteStringExtend = extend

exampleByteStringAdd ::
  forall c n. (Symbolic c, KnownNat n) => ByteString n c -> ByteString n c -> ByteString n c
exampleByteStringAdd x y = from (from x + from y :: UInt n Auto c)

exampleSHA :: SHA2 "SHA256" c n => ByteString n c -> ByteString 256 c
exampleSHA = sha2 @"SHA256"
