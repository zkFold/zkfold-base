module ZkFold.Symbolic.Cardano.Contracts.BatchTransfer where

import           Data.Maybe                                             (fromJust)
import           Data.Zip                                               (zip)
import           Numeric.Natural                                        (Natural)
import           Prelude                                                hiding (Bool, Eq (..), all, length, splitAt,
                                                                         zip, (&&), (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                                (Vector, fromVector, toVector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC                   (mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants         (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types                          (Input, Output, Transaction, paymentCredential,
                                                                         txInputs, txOutputs, txiOutput, txoAddress)
import           ZkFold.Symbolic.Compiler                               (ArithmeticCircuit, SymbolicData (pieces))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (splitCircuit)
import           ZkFold.Symbolic.Data.Bool                              (Bool, BoolType (..), all)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Types                                  (Symbolic)

type Tokens = 10
type TxOut b a = Output Tokens () b a
type TxIn b a  = Input Tokens () b a
type Tx b a = Transaction 6 0 11 Tokens () b a

class Hash a x where
    hash :: x -> a

instance SymbolicData a x => Hash (ArithmeticCircuit 1 a) x where
    hash datum =
        case fromVector $ splitCircuit (pieces datum) of
            []         -> zero
            [x]        -> mimcHash mimcConstants zero zero x
            [xL, xR]   -> mimcHash mimcConstants zero xL xR
            (xL:xR:xZ) -> mimcHash (zero : xZ ++ [zero]) zero xL xR

type Sig b a =
    (StrictConv (b 1 a) (UInt 256 b a),
     FromConstant Natural (UInt 256 b a),
     MultiplicativeSemigroup (UInt 256 b a),
     AdditiveMonoid (b 1 a),
     Symbolic (b 1 a),
     Eq (Bool (b 1 a)) (UInt 256 b a),
     Iso (UInt 256 b a) (ByteString 256 b a),
     Extend (ByteString 224 b a) (ByteString 256 b a),
     Hash (b 1 a) (TxOut b a))

verifySignature ::
    forall b a . Sig b a =>
    ByteString 224 b a ->
    (TxOut b a, TxOut b a) ->
    ByteString 256 b a ->
    Bool (b 1 a)
verifySignature pub (pay, change) sig = (from sig * base) == (strictConv mimc * from (extend pub :: ByteString 256 b a))
    where
        base :: UInt 256 b a
        base = fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural)

        mimc :: b 1 a
        mimc = mimcHash mimcConstants zero (hash pay) (hash change)

batchTransfer
    :: forall b a
    .  Eq (Bool (b 1 a)) (TxOut b a)
    => Sig b a
    => Tx b a
    -> Vector 5 (TxOut b a, TxOut b a, ByteString 256 b a)
    -> Bool (b 1 a)
batchTransfer tx transfers =
    let -- Extract the payment credentials and verify the signatures
        pkhs       = fromJust $ toVector @5 $ map (paymentCredential . txoAddress . txiOutput) $ init $ fromVector $ txInputs tx
        condition1 = all (\(pkh, (payment, change, signature)) -> verifySignature pkh (payment, change) signature) $ zip pkhs transfers
        outputs    = zip [0..] . init . fromVector $ txOutputs tx

        -- Extract the payments from the transaction and validate them
        payments   = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> even @Integer i) $ outputs

        condition2 = all (\(p', (p, _, _)) -> p' == p) $ zip payments transfers

        -- Extract the changes from the transaction and validate them
        changes    = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> odd @Integer i) $ outputs
        condition3 = all (\(c', (_, c, _)) -> c' == c) $ zip changes transfers

    in condition1 && condition2 && condition3
