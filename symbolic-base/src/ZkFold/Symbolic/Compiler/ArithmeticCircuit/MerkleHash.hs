{-# LANGUAGE DeriveAnyClass #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.MerkleHash where

import           Crypto.Hash.SHA256              (hash)
import           Data.Binary                     (Binary (..))
import           Data.ByteString                 (ByteString)
import           Data.Function                   ((.))
import           Data.Maybe                      (Maybe (..))
import           GHC.Generics                    (Generic)
import           Numeric.Natural                 (Natural)
import           Prelude                         (Integer, error)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Base.Data.ByteString     (toByteString)

newtype MerkleHash (n :: Maybe Natural) = M { runHash :: ByteString }

data Prec = Add | Mul | Div | Mod | Exp | Const deriving (Generic, Binary)

merkleHash :: Binary a => a -> MerkleHash n
merkleHash = M . hash . toByteString

instance Binary (MerkleHash n) where
  get = error "undefined"
  put = put . runHash

instance Finite (Zp n) => Finite (MerkleHash (Just n)) where
  type Order (MerkleHash (Just n)) = n

instance {-# OVERLAPPING #-} FromConstant (MerkleHash n) (MerkleHash n)

instance {-# OVERLAPPING #-} Scale (MerkleHash n) (MerkleHash n)

instance Binary a => FromConstant a (MerkleHash n) where
  fromConstant x = merkleHash (Const, x)

instance Binary a => Scale a (MerkleHash n)

instance Exponent (MerkleHash n) Natural where
  M h ^ p = merkleHash (Exp, h, hash (toByteString p))

instance MultiplicativeSemigroup (MerkleHash n) where
  M x * M y = merkleHash (Mul, x, y)

instance MultiplicativeMonoid (MerkleHash n) where
  one = fromConstant (one :: Natural)

instance AdditiveSemigroup (MerkleHash n) where
  M x + M y = merkleHash (Add, x, y)

instance AdditiveMonoid (MerkleHash n) where
  zero = fromConstant (zero :: Natural)

instance Semiring (MerkleHash n)

instance AdditiveGroup (MerkleHash (Just n)) where
  negate (M x) = merkleHash (Add, x)

instance Ring (MerkleHash (Just n))

instance Exponent (MerkleHash n) Integer where
  M h ^ p = merkleHash (Exp, h, hash (toByteString p))

instance Field (MerkleHash (Just n)) where
  finv (M x) = merkleHash (Mul, x)

instance ToConstant (MerkleHash (Just n)) where
  type Const (MerkleHash (Just n)) = MerkleHash Nothing
  toConstant = merkleHash

instance SemiEuclidean (MerkleHash Nothing) where
  div (M x) (M y) = merkleHash (Div, x, y)
  mod (M x) (M y) = merkleHash (Mod, x, y)

