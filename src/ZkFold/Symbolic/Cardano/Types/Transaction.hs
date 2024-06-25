{-# LANGUAGE DerivingVia, TypeOperators, UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types.Transaction where

import           GHC.Generics                          (Generic1, Generically1 (..), (:*:), (:.:))
import           GHC.TypeNats                          (KnownNat)
import           Prelude                               (Functor, Foldable, Traversable)

import           ZkFold.Base.Algebra.Basic.Class       (DiscreteField, FiniteField)
import           ZkFold.Base.Algebra.Basic.VectorSpace (VectorSpace)
import           ZkFold.Base.Data.Vector              (Vector)
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Data.UTCTime         (UTCTime)
import           ZkFold.Symbolic.Data.Bool             (Eq)

data Transaction inputs rinputs outputs tokens datum a = Transaction
    { txRefInputs :: (Vector rinputs :.: Input tokens datum) a
    , txInputs :: (Vector inputs :.: Input tokens datum) a
    , txOutputs :: (Vector outputs :.: Output tokens datum) a
    , txMint :: Value 1 a
    , txTimeRange :: (UTCTime :*: UTCTime) a
    } deriving stock (Functor, Foldable, Traversable, Generic1)
deriving via Generically1 (Transaction inputs rinputs outputs tokens datum)
  instance
    ( FiniteField a
    , KnownNat rinputs
    , KnownNat inputs
    , KnownNat outputs
    , KnownNat tokens
    ) => VectorSpace a (Transaction inputs rinputs outputs tokens datum)
instance
    ( FiniteField a
    , DiscreteField a
    , KnownNat rinputs
    , KnownNat inputs
    , KnownNat outputs
    , KnownNat tokens
    )
    => Eq a (Transaction inputs rinputs outputs tokens datum)
