{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Ledger.Validation.Update where

import           Data.Proxy                                    (Proxy)
import           Data.Zip                                      (Zip)
import           Prelude                                       hiding (Bool, Eq (..), all, length, splitAt, zip, (&&),
                                                                (*), (+), (++), (==), concat)
import           GHC.Generics                                  ((:*:), Par1)

import           ZkFold.Symbolic.Data.Bool                     (Bool, (&&), true)
import           ZkFold.Symbolic.Data.Class                    (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional              (bool)
import           ZkFold.Symbolic.Data.Eq                       (Eq (..))
import           ZkFold.Symbolic.Data.List                     (List, (++), singleton, concat)
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Transaction (TransactionWitness, transactionIsValid)

data UpdateWitness context = UpdateWitness
  { updateWitnessOnlineTxs :: List context (AddressIndex context, Transaction context, TransactionWitness context, Bool context)
  , updateWitnessOfflineTxs :: List context (AddressIndex context, Transaction context, TransactionWitness context)
  }

applyOnlineTransaction ::
     Signature context
  => Hashable context (AddressIndex context, Transaction context)
  => Context (AddressIndex context) ~ context
  => Support (AddressIndex context) ~ Proxy context
  => Applicative (Layout (AddressIndex context))
  => Traversable (Layout (AddressIndex context))
  => Zip  (Layout (AddressIndex context) :*: Par1)
  => SymbolicData (AddressIndex context)
  => AddressIndex context
  -> Transaction context
  -> TransactionWitness context
  -> Update context
  -> List context (Hash context)
  -> Bool context
  -> (Update context, List context (Hash context))
applyOnlineTransaction ix tx w u hashes b =
  let res = transactionIsValid (updateId u) tx w
      (newRoot, hashes') = merkleTreeAdd (hash (ix,tx)) hashes
      u' = u { updateOnlineTxsRoot = newRoot
             , updateSpentOutputs = updateSpentOutputs u ++ singleton (ix, b)
             }
   in (bool u u' res, hashes')

applyOfflineTransaction ::
     Signature context
  => Context (AddressIndex context) ~ context
  => Support (AddressIndex context)  ~ Proxy context
  => Applicative (Layout (AddressIndex context))
  => Traversable (Layout (AddressIndex context))
  => Zip (Layout (AddressIndex context, Hash context))
  => SymbolicData (AddressIndex context)
  => AddressIndex context
  -> Transaction context
  -> TransactionWitness context
  -> Update context
  -> Update context
applyOfflineTransaction ix tx w u =
   let res = transactionIsValid (updateId u) tx w
       u' = u { updateTransactions = updateTransactions u ++ singleton (ix, txId tx) }
   in bool u u' res

newUpdate ::
     Signature context
  => Hashable context (AddressIndex context, Transaction context)
  => Applicative (Layout (List context (Input context)))
  => Applicative (Layout (List context (Output context)))
  => Applicative (Layout (ContractData context))
  => Context (AddressIndex context) ~ context
  => Support (AddressIndex context)  ~ Proxy context
  => Applicative (Layout (AddressIndex context))
  => Traversable (Layout (AddressIndex context))
  => Zip (Layout (AddressIndex context, Hash context))
  => Zip  (Layout (AddressIndex context) :*: Par1)
  => SymbolicData (AddressIndex context)
  => Hash context
  -> UpdateWitness context
  -> Update context
newUpdate hsh updWitness =
   let u = emptyUpdate hsh
       (u', _) = foldl (\(updAcc, hashesAcc) (ix, tx, w, b) -> applyOnlineTransaction ix tx w updAcc hashesAcc b) (u, merkleTreeEmpty) (updateWitnessOnlineTxs updWitness)
       u'' = foldl (\acc (ix, tx, w) -> applyOfflineTransaction ix tx w acc) u' (updateWitnessOfflineTxs updWitness)
   in u''

updateIsValid ::
     Signature context
  => Hashable context (AddressIndex context, Transaction context)
  => Applicative (Layout (List context (Input context)))
  => Applicative (Layout (List context (Output context)))
  => Applicative (Layout (ContractData context))
  => Context (AddressIndex context) ~ context
  => Support (AddressIndex context)  ~ Proxy context
  => Applicative (Layout (AddressIndex context))
  => Traversable (Layout (AddressIndex context))
  => Zip (Layout (AddressIndex context, Hash context))
  => Zip  (Layout (AddressIndex context) :*: Par1)
  => SymbolicData (AddressIndex context)
  => Hash context
  -> Update context
  -> UpdateWitness context
  -> Bool context
updateIsValid uId u w =
  let txs = fmap (\(_,tx,_,_) -> tx) (updateWitnessOnlineTxs w)
          ++ fmap (\(_,tx,_) -> tx) (updateWitnessOfflineTxs w)
      mintValues = concat (txMint <$> txs)
      spentValues = txoValue . txiOutput <$> concat (txInputs <$> txs)
      prodValues = txoValue <$> concat (txOutputs <$> txs)
  in newUpdate uId w == u
  && true
    -- ^ check balance equation
