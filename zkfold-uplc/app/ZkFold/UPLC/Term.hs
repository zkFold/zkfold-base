{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module ZkFold.UPLC.Term where

import           Data.Bool                                   (Bool)
import           Data.ByteString                             (ByteString)
import           Data.Text                                   (Text)
import           Data.Word                                   (Word64)
import           Numeric.Natural                             (Natural)
import           Prelude                                     (Integer)

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (Point)
import           ZkFold.UPLC.BuiltinFunction                 (BuiltinFunction)
import           ZkFold.UPLC.BuiltinType                     (BuiltinType (..))

type ConstructorTag = Word64
type DeBruijnIndex = Natural

data Data
  = DConstr ConstructorTag [Data]
  | DMap [(Data, Data)]
  | DList [Data]
  | DI Integer
  | DB ByteString

data Constant (t :: BuiltinType) where
  CInteger :: Integer -> Constant BTInteger
  CByteString :: ByteString -> Constant BTByteString
  CString :: Text -> Constant BTString
  CBool :: Bool -> Constant BTBool
  CUnit :: () -> Constant BTUnit
  CData :: Data -> Constant BTData
  CList :: [Constant t] -> Constant (BTList t)
  CPair :: Constant t -> Constant u -> Constant (BTPair t u)
  CG1 :: Point BLS12_381_G1 -> Constant BTBLSG1
  CG2 :: Point BLS12_381_G2 -> Constant BTBLSG2

data Term
  = TVariable !DeBruijnIndex
  | forall t. TConstant !(Constant t)
  | forall s t. TBuiltin !(BuiltinFunction s t)
  | TLam {- DeBruijnIndex = 0 -} Term
  | TApp Term Term
  | TDelay Term
  | TForce Term
  | TConstr !ConstructorTag [Term]
  | TCase Term [Term]
  | TError
