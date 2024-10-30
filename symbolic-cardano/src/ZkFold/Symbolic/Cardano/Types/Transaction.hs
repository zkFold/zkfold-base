{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                              as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Class                (BaseField, Symbolic)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Input           (SymbolicInput, isValid)

data Transaction inputs rinputs outputs tokens mint datum context = Transaction {
        txRefInputs :: Vector rinputs (Input tokens datum context),
        txInputs    :: Vector inputs (Input tokens datum context),
        txOutputs   :: Vector outputs (Output tokens datum context),
        txMint      :: Value mint context,
        txTime      :: (UTCTime context, UTCTime context)
    }

deriving instance
    ( Haskell.Eq (Vector rinputs (Input tokens datum context))
    , Haskell.Eq (Vector inputs (Input tokens datum context))
    , Haskell.Eq (Vector outputs (Output tokens datum context))
    , Haskell.Eq (Value mint context)
    , Haskell.Eq (UTCTime context)
    ) => Haskell.Eq (Transaction inputs rinputs outputs tokens mint datum context)

-- TODO: Think how to prettify this abomination
instance
    ( Symbolic context
    , KnownNat tokens
    , KnownNat rinputs
    , KnownNat inputs
    , KnownNat outputs
    , KnownNat mint
    ) => SymbolicData (Transaction inputs rinputs outputs tokens mint datum context) where
  type Context (Transaction inputs rinputs outputs tokens mint datum context) = Context (Vector rinputs (Input tokens datum context), Vector inputs (Input tokens datum context), Vector outputs (Output tokens datum context), Value mint context, (UTCTime context, UTCTime context))
  type Support (Transaction inputs rinputs outputs tokens mint datum context) = Support (Vector rinputs (Input tokens datum context), Vector inputs (Input tokens datum context), Vector outputs (Output tokens datum context), Value mint context, (UTCTime context, UTCTime context))
  type Layout (Transaction inputs rinputs outputs tokens mint datum context) = Layout (Vector rinputs (Input tokens datum context), Vector inputs (Input tokens datum context), Vector outputs (Output tokens datum context), Value mint context, (UTCTime context, UTCTime context))

  pieces (Transaction a b c d e) = pieces (a, b, c, d, e)
  restore f = let (a, b, c, d, e) = restore f in Transaction a b c d e


instance
    ( Symbolic context
    , KnownNat (NumberOfRegisters (BaseField context) 32 Auto)
    , KnownNat (NumberOfRegisters (BaseField context) 64 Auto)
    , KnownNat (NumberOfRegisters (BaseField context) 11 Auto)
    , KnownNat tokens
    , KnownNat rinputs
    , KnownNat outputs
    , KnownNat mint
    , KnownNat inputs
    ) => SymbolicInput (Transaction inputs rinputs outputs tokens mint datum context) where
  isValid (Transaction _ txI _ _ _) = isValid txI
