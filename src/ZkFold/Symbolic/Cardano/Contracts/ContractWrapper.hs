{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Cardano.Contracts.ContractWrapper where

import           Prelude                                             (undefined, ($))

import           ZkFold.Base.Algebra.Basic.Class                     (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, type (+))
import           ZkFold.Base.Data.Vector                             (Vector (..), fromVector)
import           ZkFold.Base.Protocol.ARK.Plonk                      (F)
import           ZkFold.Symbolic.Cardano.Types                       (Output, OutputRef)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.Arithmetizable             (Arithmetic, SymbolicData)
import           ZkFold.Symbolic.Data.Bool                           (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.ByteString                     (ByteString)
import           ZkFold.Symbolic.Data.Combinators                    (Iso (..))
import           ZkFold.Symbolic.Data.Eq                             (Eq ((==)))
import           ZkFold.Symbolic.Data.UInt                           (UInt)
import           ZkFold.Symbolic.Data.UTCTime                        (UTCTime)

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

{-
hashFunction :: HashData inputs rinputs outputs tokens datum a -> Public a
hashFunction = undefined -- toConstant . fromConstant . blake2b_224 . serialiseData . toBuiltinData


newtype HashData inputs rinputs outputs tokens datum a = HashData
    ( Vector rinputs (OutputRef a)
    , (Vector inputs (OutputRef a)
    , (Vector outputs (Output tokens datum a)
    , (UTCTime a, UTCTime a)
    )))

deriving instance
    ( Arithmetic a
    , KnownNat inputs
    , KnownNat rinputs
    , KnownNat outputs
    , KnownNat tokens
    ) => SymbolicData a (HashData inputs rinputs outputs tokens datum (ArithmeticCircuit a))

type Contract inputs a = Vector inputs a -> Bool a
type Public a = UInt 64 a
type Privates privates a = Vector privates a

type HashFun inputs rinputs outputs tokens datum a =
    ( FromConstant (ByteString 224 a) (Public F))

-- | Use wrapper to convert circuit to plonk circuit
symbolicWrapper :: forall a privates inputs rinputs outputs tokens datum .
    ( Eq (Bool a) (Public a),
      Iso (HashData inputs rinputs outputs tokens datum a) a) =>
    Contract (privates + 1) a -> HashData inputs rinputs outputs tokens datum a -> Public a -> Privates privates a -> Bool a
symbolicWrapper contract tx hash witness =
    let -- Сhecking equality of hash and embedded data
        conditionSameHash    = hashFunction tx == hash

        -- Run the contract on one public and several private inputs
        conditionRunContract = contract $ Vector @(privates + 1) (from tx : fromVector witness)

    in conditionSameHash && conditionRunContract
-}
