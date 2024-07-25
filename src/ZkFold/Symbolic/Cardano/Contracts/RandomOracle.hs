{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           Prelude                                        hiding (Bool, Eq (..), all, length, maybe, splitAt, zip,
                                                                 (!!), (&&), (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        ((!!))
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (MiMCHash, mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Data.Bool                      (BoolType (..))
import qualified ZkFold.Symbolic.Data.ByteString                as Symbolic
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq

type Tokens = 2
type TxOut context = Output Tokens () context
type TxIn context  = Input Tokens () context
type Tx context = Transaction 1 0 2 Tokens 1 () context

hash :: forall context x . MiMCHash F context x => x -> FieldElement context
hash = mimcHash @F mimcConstants zero

type Sig context =
    ( FromConstant F (FieldElement context)
    , MultiplicativeMonoid (UInt 64 Auto context)
    , BoolType (Bool context)
    , Eq (Bool context) (FieldElement context)
    , Eq (Bool context) (UInt 64 Auto context)
    , Eq (Bool context) (ByteString 224 context)
    , Eq (Bool context) (ByteString 256 context)
    , Extend (ByteString 224 context) (ByteString 256 context)
    , Extend (AssetName context) (AssetName context)
    , BinaryExpansion (FieldElement context)
    , Bits (FieldElement context) ~ FieldElementBits context
    , MiMCHash F context (FieldElement context)
    , MiMCHash F context (OutputRef context)
    , MiMCHash F context (FieldElement context, FieldElement context))

randomOracle :: forall context . Sig context => F -> Tx context -> FieldElement context -> Bool context
randomOracle c tx w =
    let -- The secret key is correct
        conditionSecretKey = fromConstant c == hash @context w

        -- Extracting information about the transaction
        seed           = hash @context $ txiOutputRef $ txInputs tx !! 0
        Value vs       = txoTokens $ txOutputs tx !! 0
        (p, (name, n)) = vs !! 1
        policyId       = fst $ getValue (txMint tx) !! 0

        -- Computing the random number
        r = hash @context (w, seed)

        -- The token's policy is correct
        conditionPolicyId  = p == policyId

        -- The token's name is correct
        conditionTokenName = name == extend (Symbolic.ByteString $ binaryExpansion r)

        -- The token's quantity is correct
        conditionQuantity  = n == one

    in conditionSecretKey && conditionPolicyId && conditionTokenName && conditionQuantity
