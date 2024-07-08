module ZkFold.Symbolic.Ledger.Types.Basic where

import           Prelude hiding (Bool, Eq, length, splitAt, (*), (+))

{-
  Base types for used in the zkFold's ledger.
-}

-- | Finite field element.
data F context

-- | Boolean.
data Bool context

-- | Unsigned 32-bit integer.
data UInt32 context

-- | Unsigned 64-bit integer.
data UInt64 context

-- | Time in UTC.
data UTCTime context
