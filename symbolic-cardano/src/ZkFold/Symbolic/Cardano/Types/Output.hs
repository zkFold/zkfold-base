{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Output (
    module ZkFold.Symbolic.Cardano.Types.Output.Datum,
    Output(..)
) where

import           Prelude                                    hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                                    as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address      (Address)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Output.Datum
import           ZkFold.Symbolic.Cardano.Types.Value        (Value)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators           (NumberOfRegisters, RegisterSize (..))
import           ZkFold.Symbolic.Data.Eq                    (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural
import ZkFold.Symbolic.Data.Input (SymbolicInput (..))

data Output tokens datum context = Output {
        txoAddress   :: Address context,
        txoTokens    :: Value tokens context,
        txoDatumHash :: DatumHash context
    }

deriving instance
    ( Haskell.Eq (Address context)
    , Haskell.Eq (Value tokens context)
    , Haskell.Eq (DatumHash context)
    ) => Haskell.Eq (Output tokens datum context)

instance
    ( Symbolic context
    , KnownNat tokens
    ) => SymbolicData (Output tokens datum context) where

  type Context (Output tokens datum context) = Context (Address context, Value tokens context, DatumHash context)
  type Support (Output tokens datum context) = Support (Address context, Value tokens context, DatumHash context)
  type Layout (Output tokens datum context) = Layout (Address context, Value tokens context, DatumHash context)

  pieces (Output a b c) = pieces (a, b, c)
  restore f = let (a, b, c) = restore f in Output a b c

instance
    ( Symbolic context
    , KnownNat tokens
    , KnownNat (NumberOfRegisters (BaseField context) 64 Auto)
    ) => SymbolicInput (Output tokens datum context) where
    isValid (Output a t d) = isValid (a, t, d)

deriving via (Structural (Output tokens datum context))
         instance
            ( Symbolic context
            , KnownNat tokens
            , KnownNat (NumberOfRegisters (BaseField context) 64 'Auto)
            ) => Eq (Bool context) (Output tokens datum context)
