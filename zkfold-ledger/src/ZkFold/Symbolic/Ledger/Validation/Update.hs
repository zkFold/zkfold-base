{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Ledger.Validation.Update where

import           Data.Functor.Rep                              (Representable)
import           Data.Proxy                                    (Proxy)
import           Data.Zip                                      (Zip)
import           Prelude                                       hiding (Bool, Eq (..), all, concat, length, splitAt, zip,
                                                                (&&), (*), (+), (++), (==))

import           ZkFold.Symbolic.Data.Bool                     (Bool, (&&))
import           ZkFold.Symbolic.Data.Class                    (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional              (bool)
import           ZkFold.Symbolic.Data.Eq                       (Eq (..))
import           ZkFold.Symbolic.Data.List                     (List, concat, singleton, (++))
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
  => Representable (Layout (List context (Input context)))
  => Representable (Layout (List context (Output context)))
  => Representable (Layout (ContractData context))
  => Context (AddressIndex context) ~ context
  => Support (AddressIndex context)  ~ Proxy context
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
  => Context (AddressIndex context) ~ context
  => Support (AddressIndex context)  ~ Proxy context
  => Support (Value context) ~ Proxy context
  => Context (List context (Value context)) ~ context
  => Context (Value context) ~ context
  => Context (MultiAssetValue context) ~ context
  => Representable (Payload (Value context))
  => Zip (Layout (Value context))
  => SymbolicData (AddressIndex context)
  => SymbolicData (List context (Value context))
  => SymbolicData (List context (Input context))
  => SymbolicData (List context (Output context))
  => SymbolicData (Value context)
  => SymbolicData (MultiAssetValue context)
  => SymbolicData (ContractData context)
  => Representable (Payload (MultiAssetValue context))
  => Eq (Bool context) (MultiAssetValue context)
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
  && multiValueAsset (spentValues ++ mintValues) == multiValueAsset prodValues
  -- ^ TODO: make sure equality of multi-asset values is "invariant under asset reordering"
