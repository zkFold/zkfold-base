{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Ledger.Types.Value where

import           Data.Functor.Rep                      (Representable)
import           Data.Proxy                            (Proxy)
import           Data.Zip                              (Zip)
import           Prelude                               hiding (Bool, Eq, all, length, null, splitAt, (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class                 (Symbolic)
import           ZkFold.Symbolic.Data.Bool             (Bool, all)
import           ZkFold.Symbolic.Data.Class            (SymbolicData (..))
import           ZkFold.Symbolic.Data.Combinators      (RegisterSize (Auto))
import           ZkFold.Symbolic.Data.Conditional      (Conditional, bool)
import           ZkFold.Symbolic.Data.Eq               (Eq ((==)))
import           ZkFold.Symbolic.Data.List             (List, emptyList, null, singleton, uncons, (.:))
import           ZkFold.Symbolic.Data.UInt             (UInt)
import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

-- | Input to the minting contract. Usually a token name.
data Token context

-- | A minting contract is a contract that guards the minting and burning of tokens.
-- In order to mint or burn tokens, the transaction must satisfy the minting contract.
type MintingContract tx w context = Contract tx (Token context) w context

-- | A currency symbol is a hash of the minting contract that mints the tokens.
type CurrencySymbol context = ContractId context

-- | A value represents the amount of tokens that is contained in a transaction output.
-- The `ContractId` corresponds to the contract that minted the tokens with the `Token` containing the input data.
-- The `UInt64` contains the amount of tokens.
data Value context = Value
  { mintingPolicy :: CurrencySymbol context
  , tokenInstance :: Token context
  , tokenQuantity :: UInt 64 Auto context
  }

newtype MultiAssetValue context = UnsafeMultiAssetValue (List context (Value context))

emptyMultiAssetValue ::
     Symbolic context
  => Applicative (Layout (Value context))
  => MultiAssetValue context
emptyMultiAssetValue = UnsafeMultiAssetValue emptyList

-- Add a single value to a multi-asset value
addValue ::
     forall context. Conditional (Bool context) (MultiAssetValue context)
  => Symbolic context
  => SymbolicData (Value context)
  => Context (Value context) ~ context
  => Support (Value context) ~ Proxy context
  => Applicative (Layout (Value context))
  => Traversable (Layout (Value context))
  => Representable (Layout (Value context))
  => Zip (Layout (Value context))
  => Context (List context (Value context)) ~ context
  => SymbolicData (List context (Value context))
  => Traversable (Layout (List context (Value context)))
  => Representable (Layout (List context (Value context)))
  => Eq (Bool context) (CurrencySymbol context)
  => Value context
  -> MultiAssetValue context
  -> MultiAssetValue context
addValue val (UnsafeMultiAssetValue valList) =
  let oneVal = UnsafeMultiAssetValue (singleton val)
      (valHead, valTail) = uncons valList
      valHeadAdded = valHead {tokenQuantity = tokenQuantity valHead + tokenQuantity val}
      UnsafeMultiAssetValue valTailAdded = addValue val (UnsafeMultiAssetValue valTail)
      multiVal = bool @(Bool context)
        (UnsafeMultiAssetValue (valHeadAdded .: valTail))
        (UnsafeMultiAssetValue (valHead .: valTailAdded))
        (mintingPolicy val == mintingPolicy valHead)
  in bool multiVal oneVal (null valList)

-- Safe constructor for a multi-asset value
multiValueAsset ::
     Symbolic context
  => SymbolicData (Value context)
  => Context (Value context) ~ context
  => Support (Value context) ~ Proxy context
  => Applicative (Layout (Value context))
  => Traversable (Layout (Value context))
  => Representable (Layout (Value context))
  => Zip (Layout (Value context))
  => Context (List context (Value context)) ~ context
  => SymbolicData (List context (Value context))
  => Traversable (Layout (List context (Value context)))
  => Representable (Layout (List context (Value context)))
  => Eq (Bool context) (CurrencySymbol context)
  => Context (MultiAssetValue context) ~ context
  => SymbolicData (MultiAssetValue context)
  => Traversable (Layout (MultiAssetValue context))
  => Representable (Layout (MultiAssetValue context))
  => Foldable (List context)
  => List context (Value context)
  -> MultiAssetValue context
multiValueAsset = foldr addValue emptyMultiAssetValue
