{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           Prelude                                        hiding (Bool, Eq (..), all, length, maybe, splitAt, zip,
                                                                 (!!), (&&), (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        ((!!))
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (MiMCHash, mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Compiler.Arithmetizable        (Arithmetic)
import           ZkFold.Symbolic.Data.Bool                      (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt


type Tokens = 2
type TxOut b a = Output Tokens () b a
type TxIn b a  = Input Tokens () b a
type Tx b a = Transaction 1 0 2 Tokens () b a

hash :: forall a b x . (Arithmetic a, MiMCHash a b x) => x -> b 1 a
hash = mimcHash @a mimcConstants zero

type Sig b a =
    ( Arithmetic a
    , FromConstant a (b 1 a)
    , MultiplicativeMonoid (UInt 64 b a)
    , Eq (Bool (b 1 a)) (b 1 a)
    , Eq (Bool (b 1 a)) (UInt 64 b a)
    , Eq (Bool (b 1 a)) (ByteString 224 b a)
    , Eq (Bool (b 1 a)) (ByteString 256 b a)
    , Extend (Bits (b 1 a)) (b 256 a)
    , Extend (ByteString 224 b a) (ByteString 256 b a)
    , BinaryExpansion (b 1 a)
    , MiMCHash a b (b 1 a)
    , MiMCHash a b (OutputRef b a)
    , MiMCHash a b (b 1 a, b 1 a))

randomOracle :: forall a b . Sig b a => a -> Tx b a -> b 1 a -> Bool (b 1 a)
randomOracle c tx w =
    let -- The secret key is correct
        conditionSecretKey = fromConstant @a @(b 1 a) c == hash @a @_ @(b 1 a) w

        -- Extracting information about the transaction
        seed           = hash @a $ txiOutputRef $ txInputs tx !! 0 :: b 1 a
        Value vs       = txoTokens $ txOutputs tx !! 0
        (p, (name, n)) = vs !! 1
        policyId       = fst $ getValue (txMint tx) !! 0

        -- Computing the random number
        r = hash @a (w, seed) :: b 1 a

        -- The token's policy is correct
        conditionPolicyId  = p == policyId

        -- The token's name is correct
        conditionTokenName = name == ByteString (extend @_ @(b 256 a) $ binaryExpansion r)

        -- The token's quantity is correct
        conditionQuantity  = n == one

    in conditionSecretKey && conditionPolicyId && conditionTokenName && conditionQuantity
