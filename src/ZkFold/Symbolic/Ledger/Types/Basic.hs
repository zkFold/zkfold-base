module ZkFold.Symbolic.Ledger.Types.Basic where

import           Prelude                   hiding (Bool, Eq, length, splitAt, (*), (+))

import qualified ZkFold.Symbolic.Data.Bool as Symbolic
import qualified ZkFold.Symbolic.Data.List as Symbolic

{-
  Base types for used in the zkFold's ledger.
-}

-- | Boolean.
type Bool context = Symbolic.Bool (context 1)

-- | Unsigned 32-bit integer.
data UInt32 context

-- | Unsigned 64-bit integer.
data UInt64 context

-- | Time in UTC.
data UTCTime context

-- | List of elements of type `x`.
type List context = Symbolic.List context
