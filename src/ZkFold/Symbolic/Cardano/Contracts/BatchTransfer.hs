{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Cardano.Contracts.BatchTransfer where

import           Data.Foldable                                  (toList)
import           Data.Functor.Rep
import           Data.Maybe                                     (fromJust)
import           Data.Zip                                       (zip)
import           GHC.Generics                                   ((:*:) (..), (:.:) (..))
import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Bool, Eq (..), all, length, splitAt, zip, (&&),
                                                                 (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        (Vector, fromVector, toVector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHash)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types                  (Input, Output, Transaction, paymentCredential,
                                                                 txInputs, txOutputs, txiOutput, txoAddress)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Types                          (Symbolic, SymbolicData)

type TxOut = Output 10 ()
type TxIn = Input 10 ()
type Tx = Transaction 6 0 11 10 ()

hash :: (Symbolic a, SymbolicData a u) => u a -> a
hash datum = case toList datum of
    []         -> zero
    [x]        -> mimcHash mimcConstants zero zero x
    [xL, xR]   -> mimcHash mimcConstants zero xL xR
    (xL:xR:xZ) -> mimcHash (zero : xZ ++ [zero]) zero xL xR

type Sig a = (StrictConv a (UInt 256 a),
    MultiplicativeSemigroup (UInt 256 a),
    Eq a (UInt 256),
    Iso (UInt 256 a) (ByteString 256 a),
    Extend (ByteString 224 a) (ByteString 256 a),
    SymbolicData a TxOut)

verifySignature ::
    forall a . (Symbolic a, Sig a) =>
    ByteString 224 a ->
    (TxOut :*: TxOut) a ->
    ByteString 256 a ->
    Bool a
verifySignature pub (pay :*: change) sig = (from sig * base) == (strictConv mimc * from (extend pub :: ByteString 256 a))
    where
        base :: UInt 256 a
        base = fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural)

        mimc :: a
        mimc = mimcHash mimcConstants zero (hash pay) (hash change)

batchTransfer :: (Symbolic a, Eq a TxOut, Sig a) => Tx a -> (Vector 5 :.: (TxOut :*: TxOut :*: ByteString 256)) a -> Bool a
batchTransfer tx transfers =
    let -- Extract the payment credentials and verify the signatures
        pkhs       = Comp1 $ fromJust $ toVector @5 $ map (paymentCredential . txoAddress . txiOutput) $ init $ fromVector $ unComp1 $ txInputs tx
        condition1 = all (\(pkh :*: payment :*: change :*: signature) -> verifySignature pkh (payment :*: change) signature) $ zipV pkhs transfers
        outputs    = zip [0..] . init . fromVector $ unComp1 $ txOutputs tx

        zipV (Comp1 v1) (Comp1 v2) = Comp1 (mzipWithRep (:*:) v1 v2)

        -- Extract the payments from the transaction and validate them
        payments   = Comp1 $ fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> even @Integer i) $ outputs

        condition2 = all (\(p' :*: p :*: _ :*: _) -> p' == p) $ zipV payments transfers

        -- Extract the changes from the transaction and validate them
        changes    = Comp1 $ fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> odd @Integer i) $ outputs
        condition3 = all (\(c' :*: _ :*: c :*: _) -> c' == c) $ zipV changes transfers

    in condition1 && condition2 && condition3
