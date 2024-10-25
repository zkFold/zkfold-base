{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}

module ZkFold.UPLC.BuiltinFunction where

import           ZkFold.UPLC.BuiltinType (BuiltinType (..), Fin (..))

data BuiltinFunction s t
  = BFMono (BuiltinMonoFunction s t)
  | BFPoly (BuiltinPolyFunction s t)

data BuiltinMonoFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0)
  = BMFInteger (BuiltinIntegerFunction s t)
  | BMFByteString (BuiltinByteStringFunction s t)
  | BMFString (BuiltinStringFunction s t)
  | BMFAlgorithm (BuiltinAlgorithm s t)
  | BMFData (BuiltinDataFunction s t)
  | BMFCurve (BuiltinBLSFunction s t) -- ^ Batch 4
  | BMFBitwise (BuiltinBitwiseFunction s t) -- ^ Batch 5

data BuiltinPolyFunction (s :: [BuiltinType n]) (t :: BuiltinType n) where
  IfThenElse :: BuiltinPolyFunction @1 '[BTBool, BTVar Z, BTVar Z] (BTVar Z)
  ChooseUnit :: BuiltinPolyFunction @1 '[BTUnit, BTVar Z] (BTVar Z)
  Trace :: BuiltinPolyFunction @1 '[BTString, BTVar Z] (BTVar Z)
  FstPair :: BuiltinPolyFunction @2 '[BTPair (BTVar Z) (BTVar (S Z))] (BTVar Z)
  SndPair :: BuiltinPolyFunction @2 '[BTPair (BTVar Z) (BTVar (S Z))] (BTVar (S Z))
  BPFList :: BuiltinListFunction s t -> BuiltinPolyFunction s t
  ChooseData :: BuiltinPolyFunction @1 '[BTData, BTVar Z, BTVar Z, BTVar Z, BTVar Z, BTVar Z] (BTVar Z)

data BuiltinIntegerFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  AddInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  SubtractInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  MultiplyInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  DivideInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  ModInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  QuotientInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  RemainderInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTInteger
  EqualsInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTBool
  LessThanInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTBool
  LessThanEqualsInteger :: BuiltinIntegerFunction '[BTInteger, BTInteger] BTBool
  IntegerToByteString :: BuiltinIntegerFunction '[BTBool, BTInteger, BTInteger] BTByteString -- ^ Batch 4
  ByteStringToInteger :: BuiltinIntegerFunction '[BTBool, BTByteString] BTInteger -- ^ Batch 4

data BuiltinByteStringFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  AppendByteString :: BuiltinByteStringFunction '[BTByteString, BTByteString] BTByteString
  ConsByteString :: BuiltinByteStringFunction '[BTInteger, BTByteString] BTByteString
  SliceByteString :: BuiltinByteStringFunction '[BTInteger, BTInteger, BTByteString] BTByteString
  LengthOfByteString :: BuiltinByteStringFunction '[BTByteString] BTInteger
  IndexByteString :: BuiltinByteStringFunction '[BTByteString, BTInteger] BTInteger
  EqualsByteString :: BuiltinByteStringFunction '[BTByteString, BTByteString] BTBool
  LessThanByteString :: BuiltinByteStringFunction '[BTByteString, BTByteString] BTBool
  LessThanEqualsByteString :: BuiltinByteStringFunction '[BTByteString, BTByteString] BTBool

data BuiltinStringFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  AppendString :: BuiltinStringFunction '[BTString, BTString] BTString
  EqualsString :: BuiltinStringFunction '[BTString, BTString] BTBool
  EncodeUtf8 :: BuiltinStringFunction '[BTString] BTByteString
  DecodeUtf8 :: BuiltinStringFunction '[BTByteString] BTString

data BuiltinAlgorithm (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  SHA2_256 :: BuiltinAlgorithm '[BTByteString] BTByteString
  SHA3_256 :: BuiltinAlgorithm '[BTByteString] BTByteString
  Blake2b_256 :: BuiltinAlgorithm '[BTByteString] BTByteString
  VerifyEd25519Signature :: BuiltinAlgorithm '[BTByteString, BTByteString, BTByteString] BTBool
  VerifyEcdsaSecp256k1Signature :: BuiltinAlgorithm '[BTByteString, BTByteString, BTByteString] BTBool -- ^ Batch 3
  VerifySchnorrSecp256k1Signature :: BuiltinAlgorithm '[BTByteString, BTByteString, BTByteString] BTBool -- ^ Batch 3
  Blake2b_224 :: BuiltinAlgorithm '[BTByteString] BTByteString -- ^ Batch 4
  Keccak_256 :: BuiltinAlgorithm '[BTByteString] BTByteString -- ^ Batch 4
  Ripemd_160 :: BuiltinAlgorithm '[BTByteString] BTByteString -- ^ Batch 5

data BuiltinListFunction (s :: [BuiltinType n]) (t :: BuiltinType n) where
  ChooseList :: BuiltinListFunction @2 '[BTList (BTVar (S Z)), BTVar Z, BTVar Z] (BTVar Z)
  MkCons :: BuiltinListFunction @1 '[BTVar Z, BTList (BTVar Z)] (BTList (BTVar Z))
  HeadList :: BuiltinListFunction @1 '[BTList (BTVar Z)] (BTVar Z)
  TailList :: BuiltinListFunction @1 '[BTList (BTVar Z)] (BTList (BTVar Z))
  NullList :: BuiltinListFunction @1 '[BTList (BTVar Z)] BTBool

data BuiltinDataFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  ConstrData :: BuiltinDataFunction '[BTInteger, BTList BTData] BTData
  MapData :: BuiltinDataFunction '[BTList (BTPair BTData BTData)] BTData
  ListData :: BuiltinDataFunction '[BTList BTData] BTData
  IData :: BuiltinDataFunction '[BTInteger] BTData
  BData :: BuiltinDataFunction '[BTByteString] BTData
  UnConstrData :: BuiltinDataFunction '[BTData] (BTPair BTInteger (BTList BTData))
  UnMapData :: BuiltinDataFunction '[BTData] (BTList (BTPair BTData BTData))
  UnListData :: BuiltinDataFunction '[BTData] (BTList BTData)
  UnIData :: BuiltinDataFunction '[BTData] BTInteger
  UnBData :: BuiltinDataFunction '[BTData] BTByteString
  EqualsData :: BuiltinDataFunction '[BTData, BTData] BTBool
  MkPairData :: BuiltinDataFunction '[BTData, BTData] (BTPair BTData BTData)
  MkNilData :: BuiltinDataFunction '[BTUnit] (BTList BTData)
  MkNilPairData :: BuiltinDataFunction '[BTUnit] (BTList (BTPair BTData BTData))
  SerializeData :: BuiltinDataFunction '[BTData] BTByteString -- ^ Batch 2

data BuiltinBLSFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  BLS_G1 :: BuiltinBLSG1Function s t -> BuiltinBLSFunction s t
  BLS_G2 :: BuiltinBLSG2Function s t -> BuiltinBLSFunction s t
  Bls12_381_millerLoop :: BuiltinBLSFunction '[BTBLSG1, BTBLSG2] BTBLSMLResult
  Bls12_381_mulMlResult :: BuiltinBLSFunction '[BTBLSMLResult, BTBLSMLResult] BTBLSMLResult
  Bls12_381_finalVerify :: BuiltinBLSFunction '[BTBLSMLResult, BTBLSMLResult] BTBool

data BuiltinBLSG1Function (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  Bls12_381_G1_add :: BuiltinBLSG1Function '[BTBLSG1, BTBLSG1] BTBLSG1
  Bls12_381_G1_neg :: BuiltinBLSG1Function '[BTBLSG1] BTBLSG1
  Bls12_381_G1_scalarMul :: BuiltinBLSG1Function '[BTInteger, BTBLSG1] BTBLSG1
  Bls12_381_G1_equal :: BuiltinBLSG1Function '[BTBLSG1, BTBLSG1] BTBool
  Bls12_381_G1_hashToGroup :: BuiltinBLSG1Function '[BTByteString, BTByteString] BTBLSG1
  Bls12_381_G1_compress :: BuiltinBLSG1Function '[BTBLSG1] BTByteString
  Bls12_381_G1_uncompress :: BuiltinBLSG1Function '[BTByteString] BTBLSG1

data BuiltinBLSG2Function (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  Bls12_381_G2_add :: BuiltinBLSG2Function '[BTBLSG2, BTBLSG2] BTBLSG2
  Bls12_381_G2_neg :: BuiltinBLSG2Function '[BTBLSG2] BTBLSG2
  Bls12_381_G2_scalarMul :: BuiltinBLSG2Function '[BTInteger, BTBLSG2] BTBLSG2
  Bls12_381_G2_equal :: BuiltinBLSG2Function '[BTBLSG2, BTBLSG2] BTBool
  Bls12_381_G2_hashToGroup :: BuiltinBLSG2Function '[BTByteString, BTByteString] BTBLSG2
  Bls12_381_G2_compress :: BuiltinBLSG2Function '[BTBLSG2] BTByteString
  Bls12_381_G2_uncompress :: BuiltinBLSG2Function '[BTByteString] BTBLSG2

data BuiltinBitwiseFunction (s :: [BuiltinType 0]) (t :: BuiltinType 0) where
  AndByteString :: BuiltinBitwiseFunction '[BTBool, BTByteString, BTByteString] BTByteString
  OrByteString :: BuiltinBitwiseFunction '[BTBool, BTByteString, BTByteString] BTByteString
  XorByteString :: BuiltinBitwiseFunction '[BTBool, BTByteString, BTByteString] BTByteString
  ComplementByteString :: BuiltinBitwiseFunction '[BTByteString] BTByteString
  ShiftByteString :: BuiltinBitwiseFunction '[BTByteString, BTInteger] BTByteString
  RotateByteString :: BuiltinBitwiseFunction '[BTByteString, BTInteger] BTByteString
  CountSetBits :: BuiltinBitwiseFunction '[BTByteString] BTInteger
  FindFirstSetBit :: BuiltinBitwiseFunction '[BTByteString] BTInteger
  ReadBit :: BuiltinBitwiseFunction '[BTByteString, BTInteger] BTByteString
  WriteBits :: BuiltinBitwiseFunction '[BTByteString, BTList BTInteger, BTBool] BTByteString
  ReplicateByte :: BuiltinBitwiseFunction '[BTInteger, BTInteger] BTByteString
