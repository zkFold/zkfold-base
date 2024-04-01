{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.ByteString (
    ByteString(..),
) where

import           Control.Monad                                             (forM, mapM, zipWithM)
import           Data.Bits
import           Data.List                                                 (map)
import           Data.Proxy                                                (Proxy (..))
import           GHC.TypeNats                                              (KnownNat, Natural, natVal)
import           Prelude                                                   (Integer, error, ($), (.))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Prelude                                            (replicate)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, horner)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (ClosedPoly)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt

newtype ByteString (n :: Natural) a = ByteString (UInt n a)

deriving newtype instance Haskell.Show a => Haskell.Show (ByteString n a)
deriving newtype instance Haskell.Eq a => Haskell.Eq (ByteString n a)

instance (Finite p, KnownNat n) => ToConstant (ByteString n (Zp p)) Natural where
    toConstant (ByteString uint) = toConstant uint

deriving newtype instance (Finite p, KnownNat n) => Arbitrary (ByteString n (Zp p))
deriving newtype instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Natural (ByteString n a)
deriving newtype instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Integer (ByteString n a)

--------------------------------------------------------------------------------

instance (Finite p, KnownNat n) => AdditiveSemigroup (ByteString n (Zp p)) where
    -- | Bitwise or
    x + y = fromConstant @Natural $ toConstant x .|. toConstant y

instance (Finite p, KnownNat n) => AdditiveMonoid (ByteString n (Zp p)) where
    zero = fromConstant (0 :: Natural)

instance (Finite p, KnownNat n) => AdditiveGroup (ByteString n (Zp p)) where
    -- | x - y is equivalent to x + (-y), or x ∨ (¬ y)
    x - y = fromConstant @Natural $ toConstant x .|. (toConstant $ negate y)
    -- | @negate x@ is just bitwise not.
    -- @Data.Bits.complement@ is undefined for @Natural@, we have to flip bits manually.
    negate = fromConstant @Natural . (nextPow2 -) . toConstant
      where
        nextPow2 :: Natural
        nextPow2 = (2 ^ natVal (Proxy @n)) - 1

instance (Finite p, KnownNat n) => MultiplicativeSemigroup (ByteString n (Zp p)) where
    -- | Bitwise and
    x * y = fromConstant @Natural $ toConstant x .&. toConstant y

instance (Finite p, KnownNat n) => MultiplicativeMonoid (ByteString n (Zp p)) where
    -- | A ByteString with all bits set to 1 is the unity for bitwise and.
    one = negate zero

instance (Finite p, KnownNat n) => Semiring (ByteString n (Zp p))

--------------------------------------------------------------------------------

deriving newtype instance (Arithmetic a, KnownNat n) => Arithmetizable a (ByteString n (ArithmeticCircuit a))

binOp
    :: forall a n .
       Arithmetic a
    => KnownNat n
    => ByteString n (ArithmeticCircuit a)
    -> ByteString n (ArithmeticCircuit a)
    -> (forall i. i -> i -> ClosedPoly i a)
    -> ByteString n (ArithmeticCircuit a)
binOp (ByteString (UInt xs x)) (ByteString (UInt ys y)) cons =
    case circuits solve of
      []  -> error "ByteString: unreachable"
      lst -> ByteString $ UInt (Haskell.init lst) (Haskell.last lst)
  where
    solve :: forall i m. MonadBlueprint i a m => m [i]
    solve = do
        varsLeft  <- mapM runCircuit (xs Haskell.<> [x])
        varsRight <- mapM runCircuit (ys Haskell.<> [y])
        zipWithM applyBitwise varsLeft varsRight

    applyBitwise :: forall i m . MonadBlueprint i a m => i -> i -> m i
    applyBitwise l r = do
        bitsL <- expansion (registerSize @a @n) l
        bitsR <- expansion (registerSize @a @n) r
        resultBits <- zipWithM (\i j -> newAssigned $ cons i j) bitsL bitsR
        horner resultBits

instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (ByteString n (ArithmeticCircuit a)) where
    l + r = binOp l r (\i j x -> x i + x j - x i * x j)


instance (Arithmetic a, KnownNat n) => AdditiveMonoid (ByteString n (ArithmeticCircuit a)) where
    zero = ByteString $ UInt (replicate (numberOfRegisters @a @n - 1) zero) zero


instance (Arithmetic a, KnownNat n) => AdditiveGroup (ByteString n (ArithmeticCircuit a)) where
    -- | l OR (NOT r)
    -- (\i j x -> x i + (one - x j) - x i * (one - x j)) ==
    -- (\i j x -> x i + one - x j - x i * one + x i * x j)) ==
    -- (\i j x -> x i + one - x j - x i + x i * x j)) ==
    -- (\i j x -> one - x j + x i * x j))
    l - r = binOp l r (\i j x -> one - x j + x i * x j)

    negate (ByteString (UInt xs x)) = ByteString (UInt (map flipBits xs) (flipBits x))
        where
            flipBits r = circuit $ do
                i <- runCircuit r
                bits <- expansion (registerSize @a @n) i
                flipped <- forM bits $ \b -> newAssigned (\p -> one - p b)
                horner flipped


instance (Arithmetic a, KnownNat n) => MultiplicativeSemigroup (ByteString n (ArithmeticCircuit a)) where
    l * r = binOp l r (\i j x -> x i * x j)


instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (ByteString n (ArithmeticCircuit a)) where
    one = negate zero

instance (Arithmetic a, KnownNat n) => Semiring (ByteString n (ArithmeticCircuit a))
