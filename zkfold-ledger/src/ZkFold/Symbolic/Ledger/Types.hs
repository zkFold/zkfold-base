module ZkFold.Symbolic.Ledger.Types (
    module ZkFold.Symbolic.Ledger.Types.Address,
    module ZkFold.Symbolic.Ledger.Types.Basic,
    module ZkFold.Symbolic.Ledger.Types.Bridge,
    module ZkFold.Symbolic.Ledger.Types.Contract,
    module ZkFold.Symbolic.Ledger.Types.Hash,
    module ZkFold.Symbolic.Ledger.Types.Input,
    module ZkFold.Symbolic.Ledger.Types.Output,
    module ZkFold.Symbolic.Ledger.Types.OutputRef,
    module ZkFold.Symbolic.Ledger.Types.Transaction,
    module ZkFold.Symbolic.Ledger.Types.Update,
    module ZkFold.Symbolic.Ledger.Types.Value,
    Signature
) where

-- Re-exports
import           Data.Foldable                            (Foldable)
import           Data.Functor                             (Functor)
import           Data.Zip                                 (Zip)

import           ZkFold.Base.Algebra.Basic.Class          (AdditiveMonoid, MultiplicativeMonoid)
import           ZkFold.Symbolic.Class                    (Symbolic)
import           ZkFold.Symbolic.Data.Conditional         (Conditional)
import           ZkFold.Symbolic.Data.Eq                  (Eq)
import           ZkFold.Symbolic.Ledger.Types.Address
import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Bridge
import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Hash
import           ZkFold.Symbolic.Ledger.Types.Input
import           ZkFold.Symbolic.Ledger.Types.Output
import           ZkFold.Symbolic.Ledger.Types.OutputRef
import           ZkFold.Symbolic.Ledger.Types.Transaction
import           ZkFold.Symbolic.Ledger.Types.Update
import           ZkFold.Symbolic.Ledger.Types.Value

{-
    zkFold's ledger is a UTXO-based ledger. The architecture of the ledger is mostly similar to the Cardano ledger with some key differences:

    - Some transaction data is private and is kept off-chain by the concerned parties.

    - All UTXOs are locked by contracts.

    - Stake delegation and governance is implemented through contracts.
-}

type Signature context =
    ( Symbolic context
    , AdditiveMonoid (UInt32 context)
    , AdditiveMonoid (Value context)
    , Conditional (Bool context) (Update context)
    , Eq (Bool context) (Hash context)
    , Eq (Bool context) (Input context)
    , Eq (Bool context) (Address context, Datum context)
    , Eq (Bool context) (CurrencySymbol context, Token context)
    , Eq (Bool context) (Update context)
    , Eq (Bool context) (Value context)
    , Eq (Bool context) (List context (Hash context))
    , Eq (Bool context) (List context (Address context, Datum context))
    , Eq (Bool context) (List context (ContractId context, Token context))
    , Eq (Bool context) (List context (Input context))
    , Eq (Bool context) (Output context)
    , Eq (Bool context) (List context (Transaction context))
    , Eq (Bool context) (List context (List context (TransactionId context)))
    , Foldable (List context)
    , Functor (List context)
    , MultiplicativeMonoid (UInt32 context)
    , Zip (List context)
    )