module ZkFold.Symbolic.Cardano.UPLC.Builtins where

data BuiltinFunction
  = BFInteger !BuiltinIntegerFunction
  | BFByteString !BuiltinByteStringFunction
  | BFString !BuiltinStringFunction
  | BFAlgorithm !BuiltinAlgorithm
  | IfThenElse
  | ChooseUnit
  | Trace
  | BFPair !BuiltinPairFunction
  | BFList !BuiltinListFunction
  | BFData !BuiltinDataFunction
  | BFCurve !BuiltinBLSFunction -- ^ Batch 4
  | BFBitwise !BuiltinBitwiseFunction -- ^ Batch 5

data BuiltinIntegerFunction
  = AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | ModInteger
  | QuotientInteger
  | RemainderInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
  | IntegerToByteString -- ^ Batch 4
  | ByteStringToInteger -- ^ Batch 4

data BuiltinByteStringFunction
  = AppendByteString
  | ConsByteString
  | SliceByteString
  | LengthOfByteString
  | IndexByteString
  | EqualsByteString
  | LessThanByteString
  | LessThanEqualsByteString

data BuiltinStringFunction
  = AppendString
  | EqualsString
  | EncodeUtf8
  | DecodeUtf8

data BuiltinAlgorithm
  = SHA2_256
  | SHA3_256
  | Blake2b_256
  | VerifyEd25519Signature
  | VerifyEcdsaSecp256k1Signature -- ^ Batch 3
  | VerifySchnorrSecp256k1Signature -- ^ Batch 3
  | Blake2b_224 -- ^ Batch 4
  | Keccak_256 -- ^ Batch 4
  | Ripemd_160 -- ^ Batch 5

data BuiltinPairFunction = FstPair | SndPair

data BuiltinListFunction
  = ChooseList
  | MkCons
  | HeadList
  | TailList
  | NullList

data BuiltinDataFunction
  = ChooseData
  | ConstrData
  | MapData
  | ListData
  | IData
  | BData
  | UnConstrData
  | UnMapData
  | UnListData
  | UnIData
  | UnBData
  | EqualsData
  | MkPairData
  | MkNilData
  | MkNilPairData
  | SerializeData -- ^ Batch 2

data BuiltinBLSFunction
  = BLS_G1 !BuiltinBLSG1Function
  | BLS_G2 !BuiltinBLSG2Function
  | Bls12_381_millerLoop
  | Bls12_381_mulMlResult
  | Bls12_381_finalVerify

data BuiltinBLSG1Function
  = Bls12_381_G1_add
  | Bls12_381_G1_neg
  | Bls12_381_G1_scalarMul
  | Bls12_381_G1_equal
  | Bls12_381_G1_hashToGroup
  | Bls12_381_G1_compress
  | Bls12_381_G1_uncompress

data BuiltinBLSG2Function
  = Bls12_381_G2_add
  | Bls12_381_G2_neg
  | Bls12_381_G2_scalarMul
  | Bls12_381_G2_equal
  | Bls12_381_G2_hashToGroup
  | Bls12_381_G2_compress
  | Bls12_381_G2_uncompress

data BuiltinBitwiseFunction
  = AndByteString
  | OrByteString
  | XorByteString
  | ComplementByteString
  | ShiftByteString
  | RotateByteString
  | CountSetBits
  | FindFirstSetBit
  | ReadBit
  | WriteBits
  | ReplicateByte
