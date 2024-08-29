{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Output.Datum where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Algorithms.Hash.Blake2b (blake2b_256)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Data.ByteString         (emptyByteString)
import           ZkFold.Symbolic.Class                   (Symbolic)

type DatumHash context = ByteString 256 context

emptyDatumHash :: forall context . Symbolic context => DatumHash context
emptyDatumHash = blake2b_256 @0 $ emptyByteString @context
