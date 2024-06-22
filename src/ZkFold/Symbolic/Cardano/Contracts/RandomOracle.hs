module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Bool, Eq (..), all, length, splitAt, zip, (&&), (==),
                                                                 (*), (+), maybe)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        (Vector (..), fromVector)
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
    MultiplicativeSemigroup (UInt 64 a),
    MultiplicativeSemigroup (UInt 256 a),
    Eq (Bool a) (UInt 256 a),
    Eq (Bool a) (ByteString 224 a),
    Eq (Bool a) (ByteString 256 a),
    Iso (UInt 256 a) (ByteString 256 a),
    Extend (ByteString 224 a) (ByteString 256 a),
    Hash a (ByteString 256 a),
    Hash a (OutputRef a))

randomOracle :: forall a' a . (Symbolic a, Sig a, FromConstant a' a) => a' -> Tx a -> (a, a) -> Bool a
randomOracle h0 tx (w, r) =
    let -- TODO: this should be changed to the only token's policy ID that is being minted in the tx
        policyId = fromConstant (0 :: Natural)

        -- The secret key is correct
        condition1 = fromConstant @a' @a h0 == mimcHash mimcConstants zero w zero

        seed              = hash @a $ txiOutputRef $ head (fromVector $ txInputs tx)
        Value (Vector xs) = txoTokens $ head $ fromVector $ txOutputs tx
        (p, (name, _))    = xs !! 1

        -- The random number is correct
        condition2 = r == mimcHash mimcConstants zero w seed

        -- The token's name is correct
        condition3 = name == ByteString (binaryExpansion r)

        -- The token's policy is correct
        condition4 = p == policyId

    in condition1 && condition2 && condition3 && condition4