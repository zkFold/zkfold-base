{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.UInt (
    UInt(..)
) where

import           Control.Monad                                          (return, (>=>))
import           Control.Monad.State                                    (StateT (..), runStateT)
import           Data.Foldable                                          (find, foldrM, for_)
import           Data.Map                                               (fromList, (!))
import           Data.Maybe                                             (fromJust)
import           Data.Proxy                                             (Proxy (..))
import           Data.Ratio                                             ((%))
import           Data.Traversable                                       (for, traverse)
import           GHC.TypeNats                                           (KnownNat, Natural, natVal)
import           Prelude                                                (Integer, const, error, flip, map, otherwise, zip, ($), (.))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                        (Zp)
import           ZkFold.Prelude                                         (length, replicate, splitAt)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (expansion, splitExpansion)

-- TODO (Issue #18): hide this constructor
newtype UInt (n :: Natural) x = UInt [x] -- ^ registers, in little-endian
    deriving (Haskell.Show, Haskell.Eq)

--------------------------------------------------------------------------------

instance (Finite a, AdditiveSemigroup (Zp a), KnownNat n) => AdditiveSemigroup (UInt n (Zp a)) where
    UInt x + UInt y
        | numberOfRegisters @a @n Haskell.== 1 = UInt (x + y)
        | otherwise = error "UInt: TODO"

instance (Finite a, AdditiveMonoid (Zp a), KnownNat n) => AdditiveMonoid (UInt n (Zp a)) where
    zero = UInt $ replicate (numberOfRegisters @a @n) zero

instance (Finite a, AdditiveGroup (Zp a), KnownNat n) => AdditiveGroup (UInt n (Zp a)) where
    UInt x - UInt y
        | numberOfRegisters @a @n Haskell.== 1 = UInt (x - y)
        | otherwise = error "UInt: TODO"

    negate (UInt x) = UInt (map negate x)

instance (Finite a, MultiplicativeSemigroup (Zp a), KnownNat n) => MultiplicativeSemigroup (UInt n (Zp a)) where
    UInt x * UInt y
        | numberOfRegisters @a @n Haskell.== 1 = UInt (x * y)
        | otherwise = error "UInt: TODO"

instance (Finite a, MultiplicativeMonoid (Zp a), KnownNat n) => MultiplicativeMonoid (UInt n (Zp a)) where
    one = UInt $ one : replicate (numberOfRegisters @a @n - 1) zero

--------------------------------------------------------------------------------

instance (Arithmetizable a x, KnownNat n) => Arithmetizable a (UInt n x) where
    arithmetize (UInt cs) = for cs $ arithmetize >=> \case
        [i] -> expansion (registerSize @a @n) i Haskell.>> return i
        _ -> error "UInt: invalid number of circuits"

    restore cs
        | length cs Haskell.== numberOfRegisters @a @n = UInt $ map (restore . return) cs
        | otherwise = error "UInt: invalid number of values"

    typeSize = numberOfRegisters @a @n

instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt x + UInt y = UInt $ circuits $ do
        z <- newAssigned (const zero)
        (zs, c) <- flip runStateT z $ traverse StateT (Haskell.zipWith fullAdder x y)
        constraint ($ c)
        return zs
        where
            fullAdder :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullAdder xk yk c = do
                i <- runCircuit xk
                j <- runCircuit yk
                s <- newAssigned (\w -> w i + w j + w c)
                splitExpansion (registerSize @a @n) 1 s

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (UInt n (ArithmeticCircuit a)) where
    zero = UInt $ replicate (numberOfRegisters @a @n) zero

instance (Arithmetic a, KnownNat n) => AdditiveGroup (UInt n (ArithmeticCircuit a)) where
    UInt cs - UInt ds = UInt $ circuits $ do
        z <- newAssigned (const zero)
        (zs, b) <- flip runStateT z $ traverse StateT (Haskell.zipWith fullSub cs ds)
        constraint (\x -> x b - one)
        return zs
        where
            fullSub :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullSub xk yk b = do
                let (t :: a) = (one + one) ^ registerSize @a @n - one
                i <- runCircuit xk
                j <- runCircuit yk
                s <- newAssigned (\x -> x i - x j + x b + t `scale` one)
                splitExpansion (registerSize @a @n) 1 s

    negate (UInt cs) = UInt $ flip map cs $ \x -> circuit $ do
        i <- runCircuit x
        constraint ($ i)
        return i

instance (Arithmetic a, KnownNat n) => MultiplicativeSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt cs * UInt ds = UInt $ circuits $ do
        is <- for cs runCircuit
        js <- for ds runCircuit
        let xs = fromList (zip [0..] is)
            ys = fromList (zip [0..] js)
            r  = numberOfRegisters @a @n
        -- | es are pairwise products split according to target register
        es <- for [0 .. r * 2 - 2] $ \i ->
            for [Haskell.max 0 (i - r + 1) .. Haskell.min i (r - 1)] $ \j ->
                newAssigned (\x -> x (xs ! j) * x (ys ! (i - j)))
        -- | lo are pairwise products for answer, hi are overflow
        let (lo, hi) = splitAt (numberOfRegisters @a @n) es
        z <- newAssigned (const zero)
        -- | ks are output registers, c is overflow
        (ks, c) <- flip runStateT z $ for lo $ StateT . \zs c -> do
            s <- foldrM (\i j -> newAssigned (\x -> x i + x j)) c zs
            splitExpansion (registerSize @a @n) (maxOverflow @a @n) s
        -- | all overflow should be zero
        constraint ($ c)
        for_ hi $ traverse (\i -> constraint ($ i))
        return ks

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (UInt n (ArithmeticCircuit a)) where
    one = UInt $ one : replicate (numberOfRegisters @a @n - 1) zero

--------------------------------------------------------------------------------

maxOverflow :: forall a n . (Finite a, KnownNat n) => Integer
maxOverflow = registerSize @a @n + Haskell.ceiling (log2 $ numberOfRegisters @a @n)

registerSize :: forall a n . (Finite a, KnownNat n) => Integer
registerSize = Haskell.ceiling (toInteger @n % numberOfRegisters @a @n)

numberOfRegisters :: forall a n . (Finite a, KnownNat n) => Integer
numberOfRegisters = fromJust $ find (\c -> c * maxRegisterSize c Haskell.>= toInteger @n) [1 .. maxRegisterCount]
    where
        maxRegisterCount = 2 ^ bitLimit
        bitLimit = Haskell.floor $ log2 (order @a)
        maxRegisterSize regCount =
            let maxAdded = Haskell.ceiling $ log2 regCount
             in Haskell.floor $ (bitLimit - maxAdded) % (2 :: Integer)

log2 :: Integer -> Haskell.Double
log2 = Haskell.logBase 2 . Haskell.fromInteger

toInteger :: forall n . KnownNat n => Integer
toInteger = Haskell.fromIntegral $ natVal (Proxy :: Proxy n)
