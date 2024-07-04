module ZkFold.Symbolic.Cardano.Wrapper where

import           Prelude                                   hiding (Bool, Eq (..), length, splitAt, (&&), (*), (+))

import           ZkFold.Symbolic.Cardano.Types.Transaction (Transaction)
import           ZkFold.Symbolic.Data.Bool                 (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Eq                   (Eq ((==)))
import           ZkFold.Symbolic.Data.UInt                 (UInt)

{-
hashFunction :: forall inputs rinputs outputs tokens datum a .
    HashFun inputs rinputs outputs tokens datum a =>
    HashData inputs rinputs outputs tokens datum a -> Public F
hashFunction tx = fromConstant $ blake2b_224 @a (B.length b0) b
  -- where b@(BuiltinByteString b0) = serialiseData . toBuiltinData $ tx
-}

{-
hashFunction :: forall inputs rinputs outputs tokens datum a .
    (HashFun inputs rinputs outputs tokens datum a
    , FromConstant (ByteString 224 a) (Public F)
    , ToWords (ByteString (keylen * 8) a) (ByteString 8 a) ) =>
    HashData inputs rinputs outputs tokens datum a -> Public F
hashFunction tx = fromConstant $ blake2b_224 @keylen . serialiseData . toBuiltinData $ tx
-}

-- toBuiltinData :: a -> BuiltinData
-- ~
-- toBuiltinData :: HashData inputs rinputs outputs tokens datum a -> Data

-- serialiseData :: BuiltinData -> BuiltinByteString
-- ~
-- serialiseData :: Data -> ByteString (x <= 256) a

{-
blake2b_224 :: forall keylen a .
    ( KnownNat keylen
    , keylen <= 64
    , ToWords (ByteString (keylen * 8) a) (ByteString 8 a)
    , Concat (ByteString 8 a) (ByteString 224 a)
    ) => ByteString (keylen * 8) a -> ByteString 224 a
blake2b_224 = blake2b_libsodium @keylen @28
-}

type TxHash b a = UInt 64 b a

hashFunction :: Transaction inputs rinputs outputs tokens datum b a -> TxHash b a
hashFunction = undefined -- toConstant . fromConstant . blake2b_224 . serialiseData . toBuiltinData

type Contract tx redeemer backend a = tx backend a -> redeemer backend a -> Bool a

-- | Use wrapper to convert circuit to plonk circuit
symbolicContractWrapper :: forall inputs rinputs outputs tokens datum redeemer backend a .
    Eq (Bool a) (UInt 64 backend a)
    => Contract (Transaction inputs rinputs outputs tokens datum) redeemer backend a
    -> TxHash backend a
    -> Transaction inputs rinputs outputs tokens datum backend a
    -> redeemer backend a
    -> Bool a
symbolicContractWrapper contract hash tx witness =
    let -- Сhecking the supplied hash
        conditionCorrectHash      = hashFunction tx == hash :: Bool a

        -- Run the contract on one public and several private inputs
        conditionContractSucceeds = contract tx witness

    in conditionCorrectHash && conditionContractSucceeds
