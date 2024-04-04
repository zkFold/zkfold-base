{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.ByteString (
    ByteString(..),
) where

import           Control.Monad                                             (forM, mapM, zipWithM)
import           Data.Bits
import           Data.List                                                 (reverse, unfoldr)
import           Data.Maybe                                                (Maybe (..))
import           Data.Proxy                                                (Proxy (..))
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (KnownNat, Natural, natVal)
import           Prelude                                                   (Bool (..), Integer, divMod, error, fmap, head, length, otherwise, pure, tail, ($), (.), (<$>), (<*>), (==))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, fromZp)
import           ZkFold.Prelude                                            (replicate, replicateA)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, horner)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (ClosedPoly)
import           ZkFold.Symbolic.Data.Bool                                 (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators

data ByteString (n :: Natural) a = ByteString !a ![a]
    deriving (Haskell.Show, Haskell.Eq)


instance (KnownNat p, KnownNat n) => ToConstant (ByteString n (Zp p)) Natural where
  toConstant (ByteString x xs) = Haskell.foldl (\y p -> fromZp p + base * y) 0 (x:xs)
    where base = 2 ^ maxBitsPerRegister @(Zp p) @n

instance (FromConstant Natural a, Finite a, KnownNat n) => FromConstant Natural (ByteString n a) where
  fromConstant n = case reverse $ unfoldr dm (n, minNumberOfRegisters @a @n) of
                     []     -> error "FromConstant: unreachable"
                     (r:rs) -> ByteString r rs
    where
        base = 2 ^ maxBitsPerRegister @a @n

        dm :: (Natural, Natural) -> Maybe (a, (Natural, Natural))
        dm (_, 0) = Nothing
        dm (b, r) = let (d, m) = b `divMod` base in Just (fromConstant m, (d, r - 1))

instance (FromConstant Natural a, Finite a, KnownNat n) => FromConstant Integer (ByteString n a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (KnownNat p, KnownNat n) => Arbitrary (ByteString n (Zp p)) where
    arbitrary = ByteString
        <$> toss (highRegisterBits @(Zp p) @n)
        <*> replicateA (minNumberOfRegisters @(Zp p) @n - 1) (toss $ maxBitsPerRegister @(Zp p) @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)


--------------------------------------------------------------------------------

instance (KnownNat p, KnownNat n) => BoolType (ByteString n (Zp p)) where
    false = fromConstant (0 :: Natural)

    -- | A ByteString with all bits set to 1 is the unity for bitwise and.
    true = not false

    -- | bitwise not.
    -- @Data.Bits.complement@ is undefined for @Natural@, we have to flip bits manually.
    not = fromConstant @Natural . (nextPow2 -) . toConstant
      where
        nextPow2 :: Natural
        nextPow2 = (2 ^ natVal (Proxy @n)) - 1

    -- | Bitwise or
    x || y = fromConstant @Natural $ toConstant x .|. toConstant y

    -- | Bitwise and
    x && y = fromConstant @Natural $ toConstant x .&. toConstant y

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n) => Arithmetizable a (ByteString n (ArithmeticCircuit a)) where
    arithmetize (ByteString a as) = forM (a:as) runCircuit

    restore as
      | Haskell.fromIntegral (length as) == minNumberOfRegisters @a @n = ByteString (head as) (tail as)
      | otherwise = error "UInt: invalid number of values"

    typeSize = minNumberOfRegisters @a @n

binOp
    :: forall a n .
       Arithmetic a
    => KnownNat n
    => ByteString n (ArithmeticCircuit a)
    -> ByteString n (ArithmeticCircuit a)
    -> (forall i. i -> i -> ClosedPoly i a)
    -> ByteString n (ArithmeticCircuit a)
binOp (ByteString x xs) (ByteString y ys) cons =
    case circuits solve of
      []     -> error "ByteString: unreachable"
      (r:rs) -> ByteString r rs
  where
    solve :: forall i m. MonadBlueprint i a m => m [i]
    solve = do
        varsLeft  <- mapM runCircuit xs
        varsRight <- mapM runCircuit ys
        highLeft  <- runCircuit x
        highRight <- runCircuit y
        lowerRegisters <- zipWithM (applyBitwise False) varsLeft varsRight
        higherRegister <- applyBitwise True highLeft highRight
        pure $ higherRegister : lowerRegisters

    applyBitwise :: forall i m . MonadBlueprint i a m => Bool -> i -> i -> m i
    applyBitwise isHigher l r = do
        bitsL <- expansion regSize l
        bitsR <- expansion regSize r
        resultBits <- zipWithM (\i j -> newAssigned $ cons i j) bitsL bitsR
        horner resultBits
      where
         regSize = case isHigher of
                     False -> maxBitsPerRegister @a @n
                     True  -> highRegisterBits @a @n

instance (Arithmetic a, KnownNat n) => BoolType (ByteString n (ArithmeticCircuit a)) where
    false = ByteString zero (replicate (minNumberOfRegisters @a @n - 1) zero)

    true = not false

    not (ByteString x xs) = ByteString (flipBits True x) (fmap (flipBits False) xs)
        where
            flipBits isHigher r = circuit $ do
                i <- runCircuit r
                bits <- expansion (if isHigher then highRegisterBits @a @n else maxBitsPerRegister @a @n) i
                flipped <- forM bits $ \b -> newAssigned (\p -> one - p b)
                horner flipped

    l || r = binOp l r (\i j x -> x i + x j - x i * x j)

    l && r = binOp l r (\i j x -> x i * x j)

