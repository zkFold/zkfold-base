{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Output where

import           GHC.Natural                           (Natural)
import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Class       (FromConstant)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address (Address)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Value   (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString       (emptyByteString)
import           ZkFold.Symbolic.Data.Combinators      (Extend (..))
import           ZkFold.Symbolic.Data.Eq               (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural
import qualified ZkFold.Symbolic.Data.FieldElement     as FE

type DatumHash context = ByteString 256 context

emptyDatumHash :: forall context .
    ( FromConstant Natural (ByteString 0 context)
    , Extend (ByteString 0 context) (DatumHash context)
    ) => DatumHash context
emptyDatumHash = extend $ emptyByteString @context

newtype Output tokens datum context = Output (Address context, (Value tokens context, DatumHash context))

deriving instance
    KnownNat (FE.TypeSize CtxEvaluation (Value tokens CtxEvaluation))
    => FE.FieldElementData CtxEvaluation (Output tokens datum CtxEvaluation)

deriving instance
    KnownNat (TypeSize F (Value tokens CtxCompilation))
    => SymbolicData F (Output tokens datum CtxCompilation)

deriving via (Structural (Output tokens datum CtxCompilation))
         instance
            ( ts ~ TypeSize F (Output tokens datum CtxCompilation)
            , 1 <= ts
            , KnownNat ts
            , KnownNat (TypeSize F (Value tokens CtxCompilation))
            ) => Eq (Bool CtxCompilation) (Output tokens datum CtxCompilation)


txoAddress :: Output tokens datum context -> Address context
txoAddress (Output (addr, _)) = addr

txoTokens :: Output tokens datum context -> Value tokens context
txoTokens (Output (_, (v, _))) = v

txoDatumHash :: Output tokens datum context -> DatumHash context
txoDatumHash (Output (_, (_, dh))) = dh
