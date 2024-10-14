module ZkFold.Symbolic.Cardano.Types.Basic
    ( FieldElement
    , Bool
    , Symbolic.ByteString
    , Symbolic.UInt
    , Symbolic.UTCTime
    ) where

import           Prelude                           hiding (Bool, Eq, length, splitAt, (*), (+))

import qualified ZkFold.Symbolic.Data.Bool         as Symbolic
import qualified ZkFold.Symbolic.Data.ByteString   as Symbolic
import qualified ZkFold.Symbolic.Data.FieldElement as Symbolic
import qualified ZkFold.Symbolic.Data.UInt         as Symbolic
import qualified ZkFold.Symbolic.Data.UTCTime      as Symbolic

type FieldElement context     = Symbolic.FieldElement context

type Bool context = Symbolic.Bool context