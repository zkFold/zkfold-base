{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}
module ZkFold.Symbolic.Cardano.Contracts.ContractWrapper where

import           Prelude                                             (undefined, ($))

import           ZkFold.Base.Algebra.Basic.Class                     (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, type (+))
import           ZkFold.Base.Data.Vector                             (Vector (..), fromVector)
import           ZkFold.Base.Protocol.ARK.Plonk                      (F)
import           ZkFold.Symbolic.Cardano.Types.Output                (Output)
import           ZkFold.Symbolic.Cardano.Types.OutputRef             (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value                 (OneValue, Value)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.Arithmetizable             (Arithmetic, SymbolicData (..))
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

hashFunction :: HashData inputs rinputs outputs tokens datum b a -> Public b a
hashFunction = undefined -- toConstant . fromConstant . blake2b_224 . serialiseData . toBuiltinData


newtype HashData inputs rinputs outputs tokens datum b a = HashData
    ( Vector rinputs (OutputRef b a)
    , (Vector inputs (OutputRef b a)
    , (Vector outputs (Output tokens datum b a)
    , (UTCTime b a, UTCTime b a)
    )))

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (UTCTime ArithmeticCircuit a))
    , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
    , KnownNat (TypeSize a (Output tokens datum ArithmeticCircuit a))
    , KnownNat (TypeSize a (Vector outputs (Output tokens datum ArithmeticCircuit a)))
    , KnownNat (TypeSize a (OutputRef ArithmeticCircuit a))
    , KnownNat (TypeSize a (Vector inputs (OutputRef ArithmeticCircuit a)))
    , KnownNat (TypeSize a (Vector rinputs (OutputRef ArithmeticCircuit a)))
    , KnownNat (TypeSize a (OneValue ArithmeticCircuit a))
    ) => SymbolicData a (HashData inputs rinputs outputs tokens datum ArithmeticCircuit a)

type Contract inputs a = Vector inputs a -> Bool a
type Public a = UInt 64 a
type Privates privates a = Vector privates a

type HashFun inputs rinputs outputs tokens datum a b =
    ( FromConstant (ByteString 224 b a) (Public b F))

-- | Use wrapper to convert circuit to plonk circuit
contractWrapper :: forall privates inputs rinputs outputs tokens datum b a.
    ( Eq (Bool a) (Public b a),
      Iso (HashData inputs rinputs outputs tokens datum b a) a) =>
    Contract (privates + 1) a -> HashData inputs rinputs outputs tokens datum b a -> Public b a -> Privates privates a -> Bool a
contractWrapper contract tx hash witness =
    let -- Сhecking equality of hash and embedded data
        conditionSameHash    = hashFunction tx == hash

        -- Run the contract on one public and several private inputs
        conditionRunContract = contract $ Vector @(privates + 1) (from tx : fromVector witness)

    in conditionSameHash && conditionRunContract
