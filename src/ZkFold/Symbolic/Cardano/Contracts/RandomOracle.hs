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
import           ZkFold.Symbolic.Class                          (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Bool                      (BoolType (..))
import qualified ZkFold.Symbolic.Data.ByteString                as Symbolic
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq

type Tokens = 2
type TxOut context = Output Tokens () context
type TxIn context  = Input Tokens () context
type Tx context = Transaction 1 0 2 Tokens 1 () context

hash :: forall context x . (Symbolic context, MiMCHash (BaseField context) context x )=> x -> FieldElement context
hash = mimcHash @(BaseField context) mimcConstants zero

randomOracle :: forall context .
    ( Symbolic context
    , FromConstant (BaseField context) (FieldElement context)
    , Bits (FieldElement context) ~ FieldElementBits context
    ) => BaseField context -> Tx context -> FieldElement context -> Bool context
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
