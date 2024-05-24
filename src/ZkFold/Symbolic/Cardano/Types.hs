{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types where

import           GHC.Generics                       hiding (UInt)
import           Data.Functor.Identity
import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime

newtype Transaction inputs rinputs outputs tokens datum a = Transaction
    ( (   (Vector rinputs :.: Input tokens datum)
      :*: (Vector inputs :.: Input tokens datum)
      :*: (Vector outputs :.: Output tokens datum)
      :*: UTCTime :*: UTCTime
      ) a
    )
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving newtype instance
  ( KnownNat rinputs
  , KnownNat inputs
  , KnownNat outputs
  , KnownNat tokens
  , FiniteField a
  ) => VectorSpace a (Transaction inputs rinputs outputs tokens datum)
instance 
  ( KnownNat rinputs
  , KnownNat inputs
  , KnownNat outputs
  , KnownNat tokens
  , DiscreteField a
  , FiniteField a
  ) => Eq a (Transaction inputs rinputs outputs tokens datum)

txInputs :: Transaction inputs rinputs outputs tokens datum a -> (Vector inputs :.: Input tokens datum) a
txInputs (Transaction (_ :*: is :*: _)) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum a -> (Vector outputs :.: Output tokens datum) a
txOutputs (Transaction (_ :*: _ :*: os :*: _)) = os

newtype TxId a = TxId a
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving via Identity instance VectorSpace a TxId
instance DiscreteField a => Eq a TxId

newtype Value n a = Value ((Vector n :.: (ByteString 224 :*: ByteString 256 :*: UInt 64)) a)
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving newtype instance (KnownNat n, FiniteField a) => VectorSpace a (Value n)
instance (KnownNat n, DiscreteField a, FiniteField a) => Eq a (Value n)

newtype Input tokens datum a = Input ((OutputRef :*: Output tokens datum) a)
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving newtype instance (KnownNat tokens, FiniteField a) => VectorSpace a (Input tokens datum)
instance (KnownNat tokens, DiscreteField a, FiniteField a) => Eq a (Input tokens datum)

txiOutput :: Input tokens datum a -> Output tokens datum a
txiOutput (Input (_ :*: txo)) = txo

txiDatumHash :: Input tokens datum a -> ByteString 256 a
txiDatumHash (Input (_ :*: txo)) = txoDatumHash txo

newtype Output tokens datum a = Output ((Address :*: Value tokens :*: ByteString 256) a)
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving newtype instance (KnownNat tokens, FiniteField a) => VectorSpace a (Output tokens datum)
instance (KnownNat tokens, DiscreteField a, FiniteField a) => Eq a (Output tokens datum)

txoAddress :: Output tokens datum a -> Address a
txoAddress (Output (addr :*: _)) = addr

txoDatumHash :: Output tokens datum a -> ByteString 256 a
txoDatumHash (Output (_ :*: _ :*: dh)) = dh

newtype OutputRef a = OutputRef ((TxId :*: UInt 32) a)
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving newtype instance FiniteField a => VectorSpace a OutputRef
instance (DiscreteField a, FiniteField a) => Eq a OutputRef

newtype Address a = Address ((ByteString 4 :*: ByteString 224 :*: ByteString 224) a)
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving newtype instance FiniteField a => VectorSpace a Address
instance (DiscreteField a, FiniteField a) => Eq a Address

paymentCredential :: Address a -> ByteString 224 a
paymentCredential (Address (_ :*: pc :*: _)) = pc

newtype DatumHash datum a = DatumHash a
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving via Identity instance VectorSpace a (DatumHash datum)

newtype ScriptHash a = ScriptHash a
    deriving stock
        ( Prelude.Eq
        , Prelude.Show
        , Prelude.Functor
        , Prelude.Foldable
        , Prelude.Traversable
        )
deriving via Identity instance VectorSpace a ScriptHash
