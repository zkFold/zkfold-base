module ZkFold.Symbolic.Cardano.Contracts.BatchTransfer where

import           Data.Maybe                       (fromJust)
import           Data.Zip                         (zip)
import           Prelude                          hiding (Bool, Eq(..), length, splitAt, zip, all, (*), (+))

import           ZkFold.Base.Data.Vector          (Vector, fromVector, toVector)
import           ZkFold.Symbolic.Cardano.Types    (Transaction, Output, Input, txInputs, txiOutput, txoAddress, paymentCredential, txOutputs)
import           ZkFold.Symbolic.Data.Bool        (Bool, all)
import           ZkFold.Symbolic.Data.ByteString  (ByteString)
import           ZkFold.Symbolic.Types            (Symbolic)

type TxOut a = Output 10 () a
type TxIn a  = Input 10 () a
type Tx a = Transaction 6 0 11 10 () a

verifySignature :: ByteString 224 a -> (TxOut a, TxOut a) -> ByteString 256 a -> Bool a
verifySignature = undefined

batchTransfer :: Symbolic a => Tx a -> Vector 5 (TxOut a, TxOut a, ByteString 256 a) -> Bool a
batchTransfer tx transfers =
    let -- Extract the payment credentials and verify the signatures
        pkhs       = fromJust $ toVector @5 $ map (paymentCredential . txoAddress . txiOutput) $ init $ fromVector $ txInputs tx
        condition1 = all (\(pkh, (payment, change, signature)) -> verifySignature pkh (payment, change) signature) $ zip pkhs transfers

        -- Extract the payments from the transaction and validate them
        payments   = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> even @Integer i) $ zip [0..] (init $ fromVector $ txOutputs tx)
        -- condition2 = all (\(p', (p, _, _)) -> p' == p) $ zip payments transfers

        -- Extract the changes from the transaction and validate them
        changes    = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> odd @Integer i) $ zip [0..] (init $ fromVector $ txOutputs tx)
        -- condition3 = all (\(c', (_, c, _)) -> c' == c) $ zip changes transfers

    in condition1 -- && condition2 && condition3