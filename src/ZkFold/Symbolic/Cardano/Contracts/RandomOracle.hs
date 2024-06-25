{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           Data.Kind                            (Constraint, Type)
import           GHC.Generics                         (Par1 (..), (:*:) (..))
import           GHC.TypeNats                         (KnownNat, type (<=))
import           Prelude                              hiding (Bool, Eq (..), all, length, maybe, splitAt, zip, (!!),
                                                       (&&), (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.MiMC (hash)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Data.Bool            (Bool, Boolean (..), Eq (..))
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.Vector          ((!!))
import           ZkFold.Symbolic.Types                (Symbolic)

type Tokens = 2
type TxOut = Output Tokens ()
type TxIn = Input Tokens ()
type Tx = Transaction 1 0 2 Tokens ()

type Sig :: Type -> Constraint
type Sig a =
  ( forall n. KnownNat n => StrictConv a (UInt n a)
  , forall n. KnownNat n => MultiplicativeMonoid (UInt n a)
  , forall n. KnownNat n => Eq a (UInt n)
  , forall n. KnownNat n => Iso (UInt n a) (ByteString n a)
  , forall n. KnownNat n => Eq a (ByteString n)
  , forall m n. (KnownNat n, m <= n) => Extend (ByteString m a) (ByteString n a)
  )

randomOracle
  :: forall a' a w. (Symbolic a, Sig a, FromConstant a' a, Foldable w)
  => a'
  -> Tx a
  -> w a
  -> Bool a
randomOracle c tx w =
    let -- The secret key is correct
        conditionSecretKey = Par1 (fromConstant c) == Par1 (hash w)

        -- Extracting information about the transaction
        seed            = hash @a (txInputs tx !! 0)
        Value p name n  = (txoTokens (txOutputs tx !! 0)) !! 1
        Value{policyId} = txMint tx

        -- Computing the random number
        r = hash (w :*: Par1 seed)

        -- The token's policy is correct
        conditionPolicyId  = p == policyId

        -- The token's name is correct
        conditionTokenName = name == ByteString (binaryExpansion r)

        -- The token's quantity is correct
        conditionQuantity  = n == one

    in conditionSecretKey && conditionPolicyId && conditionTokenName && conditionQuantity
