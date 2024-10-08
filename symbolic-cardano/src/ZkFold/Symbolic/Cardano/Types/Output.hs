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
import           ZkFold.Symbolic.Cardano.Types.Value        (SingleAsset, Value)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Eq                    (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural

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
    , KnownNat (TypeSize (Value tokens context))
    , KnownNat (TypeSize (SingleAsset context))
    , KnownNat tokens
    ) => SymbolicData (Output tokens datum context) where

  type Context (Output tokens datum context) = Context (Address context, Value tokens context, DatumHash context)
  type Support (Output tokens datum context) = Support (Address context, Value tokens context, DatumHash context)
  type TypeSize (Output tokens datum context) = TypeSize (Address context, Value tokens context, DatumHash context)

  pieces (Output a b c) = pieces (a, b, c)
  restore f = let (a, b, c) = restore f in Output a b c

deriving via (Structural (Output tokens datum context))
         instance
            ( Symbolic context
            , KnownNat tokens
            , KnownNat (TypeSize (SingleAsset context))
            , KnownNat (TypeSize (Value tokens context))
            ) => Eq (Bool context) (Output tokens datum context)
