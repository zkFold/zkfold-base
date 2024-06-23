module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           Prelude                                        hiding (Bool, Eq (..), all, length, maybe, splitAt, zip,
                                                                 (!!), (&&), (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        ((!!))
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Compiler                       (ArithmeticCircuit, SymbolicData (..))
import           ZkFold.Symbolic.Data.Bool                      (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Types                          (Symbolic)

type Tokens = 2
type TxOut a = Output Tokens () a
type TxIn a  = Input Tokens () a
type Tx a = Transaction 1 0 2 Tokens () a

class Hash a x where
    hash :: x -> a

instance SymbolicData a x => Hash (ArithmeticCircuit a) x where
    hash datum = case pieces datum of
        []         -> zero
        [x]        -> mimcHash mimcConstants zero zero x
        [xL, xR]   -> mimcHash mimcConstants zero xL xR
        (xL:xR:xZ) -> mimcHash (zero : xZ ++ [zero]) zero xL xR

type Sig a = (StrictConv a (UInt 256 a),
    MultiplicativeMonoid (UInt 64 a),
    MultiplicativeSemigroup (UInt 256 a),
    Eq (Bool a) (UInt 64 a),
    Eq (Bool a) (UInt 256 a),
    Eq (Bool a) (ByteString 224 a),
    Eq (Bool a) (ByteString 256 a),
    Iso (UInt 256 a) (ByteString 256 a),
    Extend (ByteString 224 a) (ByteString 256 a),
    Hash a (ByteString 256 a),
    Hash a (OutputRef a))

randomOracle :: forall a' a . (Symbolic a, Sig a, FromConstant a' a) => a' -> Tx a -> a -> Bool a
randomOracle c tx w =
    let -- The secret key is correct
        conditionSecretKey = fromConstant @a' @a c == mimcHash mimcConstants zero w zero

        -- Extracting information about the transaction
        seed           = hash @a $ txiOutputRef $ txInputs tx !! 0
        Value vs       = txoTokens $ txOutputs tx !! 0
        (p, (name, n)) = vs !! 1
        policyId          = fst $ getValue (txMint tx) !! 0

        -- Computing the random number
        r = mimcHash mimcConstants zero w seed

        -- The token's policy is correct
        conditionPolicyId  = p == policyId

        -- The token's name is correct
        conditionTokenName = name == ByteString (binaryExpansion r)

        -- The token's quantity is correct
        conditionQuantity  = n == one

    in conditionSecretKey && conditionPolicyId && conditionTokenName && conditionQuantity
