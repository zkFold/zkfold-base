{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           Prelude                                                hiding (Bool, Eq (..), all, length, maybe,
                                                                         splitAt, zip, (!!), (&&), (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                                (fromVector, (!!))
import           ZkFold.Symbolic.Algorithms.Hash.MiMC                   (mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants         (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Compiler                               (ArithmeticCircuit, SymbolicData (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (splitCircuit)
import           ZkFold.Symbolic.Data.Bool                              (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Types                                  (Symbolic)

type Tokens = 2
type TxOut b a = Output Tokens () b a
type TxIn b a  = Input Tokens () b a
type Tx b a = Transaction 1 0 2 Tokens () b a

class Hash a x where
    hash :: x -> a

instance SymbolicData a x => Hash (ArithmeticCircuit 1 a) x where
    hash datum = case fromVector $ splitCircuit (pieces datum) of
        []         -> zero
        [x]        -> mimcHash mimcConstants zero zero x
        [xL, xR]   -> mimcHash mimcConstants zero xL xR
        (xL:xR:xZ) -> mimcHash (zero : xZ ++ [zero]) zero xL xR

type Sig b a = (StrictConv a (UInt 256 b a),
    MultiplicativeMonoid (UInt 64 b a),
    MultiplicativeSemigroup (UInt 256 b a),
    Eq (Bool (b 1 a)) a,
    Eq (Bool (b 1 a)) (UInt 64 b a),
    Eq (Bool (b 1 a)) (UInt 256 b a),
    Eq (Bool (b 1 a)) (ByteString 224 b a),
    Eq (Bool (b 1 a)) (ByteString 256 b a),
    Iso (UInt 256 b a) (ByteString 256 b a),
    Extend (ByteString 224 b a) (ByteString 256 b a),
    BinaryExpansion a, Bits a ~ b 256 a,
    Hash a (ByteString 256 b a),
    Hash a (OutputRef b a))

randomOracle :: forall a' a b . (Symbolic a, Sig b a, FromConstant a' a) => a' -> Tx b a -> a -> Bool (b 1 a)
randomOracle c tx w =
    let -- The secret key is correct
        conditionSecretKey = fromConstant @a' @a c == mimcHash mimcConstants zero w zero

        -- Extracting information about the transaction
        seed           = hash @a $ txiOutputRef $ txInputs tx !! 0
        Value vs       = txoTokens $ txOutputs tx !! 0
        (p, (name, n)) = vs !! 1
        policyId       = fst $ getValue (txMint tx) !! 0

        -- Computing the random number
        r = mimcHash mimcConstants zero w seed

        -- The token's policy is correct
        conditionPolicyId  = p == policyId

        -- The token's name is correct
        conditionTokenName = name == ByteString (binaryExpansion r)

        -- The token's quantity is correct
        conditionQuantity  = n == one

    in conditionSecretKey && conditionPolicyId && conditionTokenName && conditionQuantity
