module ZkFold.Symbolic.Cardano.Contracts.BatchTransfer where

import           Data.Maybe                                     (fromJust)
import           Data.Functor.Rep                               (mzipRep)
import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Bool, Eq (..), all, length, splitAt, (&&),
                                                                 (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        (Vector, fromVector, toVector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types                  (Input, Output, Transaction, paymentCredential,
                                                                 txInputs, txOutputs, txiOutput, txoAddress)
import           ZkFold.Symbolic.Compiler                       (ArithmeticCircuit, SymbolicData (pieces))
import qualified ZkFold.Symbolic.Data.Algebra                   as Alg
import           ZkFold.Symbolic.Data.Bool                      (Bool, BoolType (..), all)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Types                          (Symbolic)

type TxOut a = Output 10 () a
type TxIn a  = Input 10 () a
type Tx a = Transaction 6 0 11 10 () a

class Hash a x where
    hash :: x -> a

instance SymbolicData a x => Hash (ArithmeticCircuit a) x where
    hash datum = case pieces datum of
        []         -> zero
        [x]        -> mimcHash mimcConstants zero zero x
        [xL, xR]   -> mimcHash mimcConstants zero xL xR
        (xL:xR:xZ) -> mimcHash (zero : xZ ++ [zero]) zero xL xR

type Sig a = (StrictConv a (UInt 256 a),
    Alg.MultiplicativeSemigroup a (UInt 256),
    Eq (Bool a) (UInt 256 a),
    Iso (UInt 256 a) (ByteString 256 a),
    Extend (ByteString 224 a) (ByteString 256 a),
    Hash a (TxOut a))

verifySignature ::
    forall a . (Symbolic a, Sig a) =>
    ByteString 224 a ->
    (TxOut a, TxOut a) ->
    ByteString 256 a ->
    Bool a
verifySignature pub (pay, change) sig = (from sig Alg.* base) == (strictConv mimc Alg.* from (extend pub :: ByteString 256 a))
    where
        base :: UInt 256 a
        base = fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural)

        mimc :: a
        mimc = mimcHash mimcConstants zero (hash pay) (hash change)

batchTransfer :: (Symbolic a, Eq (Bool a) (TxOut a), Sig a) => Tx a -> Vector 5 (TxOut a, TxOut a, ByteString 256 a) -> Bool a
batchTransfer tx transfers =
    let -- Extract the payment credentials and verify the signatures
        pkhs       = fromJust $ toVector @5 $ map (paymentCredential . txoAddress . txiOutput) $ init $ fromVector $ txInputs tx
        condition1 = all (\(pkh, (payment, change, signature)) -> verifySignature pkh (payment, change) signature) $ mzipRep pkhs transfers
        outputs    = zip [0..] . init . fromVector $ txOutputs tx

        -- Extract the payments from the transaction and validate them
        payments   = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> even @Integer i) $ outputs

        condition2 = all (\(p', (p, _, _)) -> p' == p) $ mzipRep payments transfers

        -- Extract the changes from the transaction and validate them
        changes    = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> odd @Integer i) $ outputs
        condition3 = all (\(c', (_, c, _)) -> c' == c) $ mzipRep changes transfers

    in condition1 && condition2 && condition3
