{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Output.Datum where

import           GHC.Natural                             (Natural)
import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Class         (AdditiveGroup, FromConstant, MultiplicativeMonoid)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b (blake2b_256)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Data.Bool               (BoolType)
import           ZkFold.Symbolic.Data.ByteString         (Concat, ReverseEndianness, ShiftBits, ToWords, Truncate,
                                                          emptyByteString)
import           ZkFold.Symbolic.Data.Combinators        (Extend (..), Iso, RegisterSize (..))

type DatumHash context = ByteString 256 context

emptyDatumHash :: forall context .
    ( Iso (UInt 64 Auto context) (ByteString 64 context)
    , ShiftBits (ByteString 64 context)
    , ShiftBits (ByteString 1024 context)
    , Concat (ByteString 64 context) (ByteString 512 context)
    , ReverseEndianness 64 (ByteString 512 context)
    , ReverseEndianness 64 (ByteString 1024 context)
    , BoolType (ByteString 64 context)
    , AdditiveGroup (UInt 64 Auto context)
    , FromConstant Natural (ByteString 0 context)
    , FromConstant Natural (UInt 64 Auto context)
    , MultiplicativeMonoid (UInt 64 Auto context)
    , Extend (ByteString 0 context) (ByteString 1024 context)
    , ToWords (ByteString 1024 context) (ByteString 64 context)
    , Truncate (ByteString 512 context) (ByteString 256 context)
    ) => DatumHash context
emptyDatumHash = blake2b_256 @0 $ emptyByteString @context
