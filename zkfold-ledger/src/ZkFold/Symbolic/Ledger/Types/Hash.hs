module ZkFold.Symbolic.Ledger.Types.Hash where

import           Prelude hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.FieldElement (FieldElement)

-- | Hash type used in the zkFold ledger.
type Hash = FieldElement

class Hashable context x where
  hash :: x -> Hash context
