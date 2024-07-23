module ZkFold.Symbolic.Ledger.Types.Basic (Bool, UInt32, UInt64, UTCTime, List) where

import           Prelude                   hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.Bool (Bool)
import           ZkFold.Symbolic.Data.List (List)

{-
  Base types for used in the zkFold's ledger.
-}

-- | Unsigned 32-bit integer.
data UInt32 context

-- | Unsigned 64-bit integer.
data UInt64 context

-- | Time in UTC.
data UTCTime context
