{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Output (
    module ZkFold.Symbolic.Cardano.Types.Output.Datum,
    Output(..),
    txoAddress,
    txoTokens,
    txoDatumHash
) where

import           Data.Functor.Rep                    (Representable (..))
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

newtype Output tokens datum context = Output (Address context, (Value tokens context, DatumHash context))

deriving instance
    ( Haskell.Eq (Address context)
    , Haskell.Eq (Value tokens context)
    , Haskell.Eq (DatumHash context)
    ) => Haskell.Eq (Output tokens datum context)

deriving instance
    ( Symbolic context
    , KnownNat (TypeSize context (Value tokens context))
    , KnownNat (TypeSize context (SingleAsset context))
    , KnownNat tokens
    ) => SymbolicData context (Output tokens datum context)

deriving via (Structural (Output tokens datum (CtxCompilation i)))
         instance
            ( ts ~ TypeSize (CtxCompilation i) (Output tokens datum (CtxCompilation i))
            , 1 <= ts
            , KnownNat tokens
            , KnownNat (TypeSize (CtxCompilation i) (Value tokens (CtxCompilation i)))
            , Ord (Rep i)
            , Representable i
            ) => Eq (Bool (CtxCompilation i)) (Output tokens datum (CtxCompilation i))

txoAddress :: Output tokens datum context -> Address context
txoAddress (Output (addr, _)) = addr

txoTokens :: Output tokens datum context -> Value tokens context
txoTokens (Output (_, (v, _))) = v

txoDatumHash :: Output tokens datum context -> DatumHash context
txoDatumHash (Output (_, (_, dh))) = dh
