module ZkFold.Symbolic.Cardano.Contracts.ZkPass where
import           Prelude                          hiding (Bool, Eq (..), length, splitAt, (&&), (*), (+))

import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Class            (Symbolic)
import           ZkFold.Symbolic.Data.Bool        (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators (Iso (..), RegisterSize (..))
import           ZkFold.Symbolic.Data.Eq          (Eq ((==)))

type TxHash context = UInt 32 Auto context

newtype ZKPassPublicFields context = PublicFields (context [])

data ZKPassResult c = ZKPassResult
  { allocatorAddress   :: ByteString 32 c
  , allocatorSignature :: ByteString 32 c
  , publicFields       :: ZKPassPublicFields c
  , publicFieldsHash   :: ByteString 32 c
  , taskId             :: ByteString 32 c
  , uHash              :: ByteString 32 c
  , validatorAddress   :: ByteString 32 c
  , validatorSignature :: ByteString 32 c
  }

hashFunction :: ZKPassPublicFields context -> TxHash context
hashFunction = undefined

verifyAllocatorSignature :: forall c . (Symbolic c, Eq (Bool c) (TxHash c)) => TxHash c -> TxHash c -> TxHash c -> TxHash c -> Bool c
verifyAllocatorSignature taskId validatorAddress allocatorAddress allocatorSignature =
    allocatorAddress == allocatorSignature

verifyValidatorSignature :: forall c . (Symbolic c, Eq (Bool c) (TxHash c)) => TxHash c -> TxHash c -> TxHash c -> TxHash c -> TxHash c -> Bool c
verifyValidatorSignature taskId uHash publicFieldsHash validatorAddress validatorSignature =
    validatorAddress == validatorSignature

zkPassSymbolicVerifier ::
    forall context
    . (Symbolic context
    , Eq (Bool context) (TxHash context)
    ) => ZKPassResult context -> Bool context
zkPassSymbolicVerifier (ZKPassResult
    allocatorAddress
    allocatorSignature
    publicFields
    publicFieldsHash
    taskId
    uHash
    validatorAddress
    validatorSignature
   ) =
    let
        conditionAllocatorSignatureCorrect = verifyAllocatorSignature
            (from taskId) (from validatorAddress) (from allocatorAddress) (from allocatorSignature)

        conditionHashEquality = hashFunction publicFields == from publicFieldsHash

        conditionValidatorSignatureCorrect = verifyValidatorSignature
            (from taskId) (from uHash) (from publicFieldsHash) (from validatorAddress) (from validatorSignature)

    in conditionAllocatorSignatureCorrect && conditionHashEquality && conditionValidatorSignatureCorrect


