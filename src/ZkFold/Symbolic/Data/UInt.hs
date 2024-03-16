{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.UInt (
    UInt(..),
    toInteger
) where

import           Control.Applicative                                    ((<*>))
import           Control.Monad.State                                    (StateT (..))
import           Data.Foldable                                          (find, foldr, foldrM, for_)
import           Data.Functor                                           ((<$>))
import           Data.List                                              (map, unfoldr, zip, zipWith)
import           Data.Map                                               (fromList, (!))
import           Data.Maybe                                             (fromMaybe)
import           Data.Proxy                                             (Proxy (..))
import           Data.Ratio                                             ((%))
import           Data.Traversable                                       (for, traverse)
import           Data.Tuple                                             (swap)
import           GHC.TypeNats                                           (KnownNat, Natural, natVal)
import           Prelude                                                (Integer, error, flip, otherwise, return, ($), (++), (.), (>>=))
import qualified Prelude                                                as Haskell
import           Test.QuickCheck                                        (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                        (Zp, fromZp)
import           ZkFold.Prelude                                         (length, replicate, replicateA, splitAt)
import           ZkFold.Symbolic.Compiler                               hiding (forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (expansion, splitExpansion)

-- TODO (Issue #18): hide this constructor
data UInt (n :: Natural) a = UInt ![a] !a
    deriving (Haskell.Show, Haskell.Eq)

instance (FromConstant Integer a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Integer (UInt n a) where
    fromConstant n
        | n Haskell.< 0 = error "n is negative"
        | otherwise =
            let base = 2 ^ registerSize @a @n
                redex = map fromConstant $ flip unfoldr n $ \case
                    0 -> Haskell.Nothing
                    x -> Haskell.Just (swap $ x `Haskell.divMod` base)
                r = numberOfRegisters @a @n - 1
            in case greedySplitAt r redex of
                (lo, [hi]) -> UInt lo hi
                (lo, [])   -> UInt (lo ++ replicate (r - length lo) zero) zero
                (_, _)     -> error "number is too big"

greedySplitAt :: Integer -> [a] -> ([a], [a])
greedySplitAt 0 xs = ([], xs)
greedySplitAt _ [] = ([], [])
greedySplitAt n (x : xs) =
    let (ys, zs) = greedySplitAt (n - 1) xs
     in (x : ys, zs)

--------------------------------------------------------------------------------

toInteger :: forall p n . (Finite p, KnownNat n) => UInt n (Zp p) -> Integer
toInteger (UInt xs x) = foldr (\p y -> fromZp p + base * y) 0 (xs ++ [x])
    where base = 2 ^ registerSize @p @n

instance (Finite p, KnownNat n) => AdditiveSemigroup (UInt n (Zp p)) where
    x + y = fromConstant $ toInteger x + toInteger y

instance (Finite p, KnownNat n) => AdditiveMonoid (UInt n (Zp p)) where
    zero = fromConstant (0 :: Integer)

instance (Finite p, KnownNat n) => AdditiveGroup (UInt n (Zp p)) where
    x - y = fromConstant $ toInteger x - toInteger y
    negate = fromConstant . negate . toInteger

instance (Finite p, KnownNat n) => MultiplicativeSemigroup (UInt n (Zp p)) where
    x * y = fromConstant $ toInteger x * toInteger y

instance (Finite p, KnownNat n) => MultiplicativeMonoid (UInt n (Zp p)) where
    one = fromConstant (1 :: Integer)

instance (Finite p, KnownNat n) => Arbitrary (UInt n (Zp p)) where
    arbitrary = UInt
        <$> replicateA (numberOfRegisters @p @n - 1) (toss $ registerSize @p @n)
        <*> toss (highRegisterSize @p @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n) => Arithmetizable a (UInt n (ArithmeticCircuit a)) where
    arithmetize (UInt as a) = for (as ++ [a]) runCircuit

    restore as = case splitAt (numberOfRegisters @a @n - 1) as of
        (lo, [hi]) -> UInt lo hi
        (_, _)     -> error "UInt: invalid number of values"

    typeSize = numberOfRegisters @a @n

instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt [] x + UInt [] y = UInt [] $ circuit $ do
        z <- runCircuit (x + y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

    UInt (x : xs) z + UInt (y : ys) w =
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                (i, j) <- runCircuit (x + y) >>= splitExpansion (registerSize @a @n) 1
                (zs, c) <- flip runStateT j $ traverse StateT (zipWith fullAdder xs ys)
                k <- fullAdded z w c
                _ <- expansion (highRegisterSize @a @n) k
                return (k : i : zs)

            fullAdder :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullAdder xk yk c = fullAdded xk yk c >>= splitExpansion (registerSize @a @n) 1

            fullAdded :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m i
            fullAdded xk yk c = do
                i <- runCircuit xk
                j <- runCircuit yk
                newAssigned (\v -> v i + v j + v c)

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    UInt _ _ + UInt _ _ = error "UInt: unreachable"

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (UInt n (ArithmeticCircuit a)) where
    zero = UInt (replicate (numberOfRegisters @a @n - 1) zero) zero

instance (Arithmetic a, KnownNat n) => AdditiveGroup (UInt n (ArithmeticCircuit a)) where
    UInt [] x - UInt [] y = UInt [] $ circuit $ do
        z <- runCircuit (x - y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

    UInt (x : xs) z - UInt (y : ys) w =
        let t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                s <- newAssigned (\v -> v i - v j + (t + one) `scale` one)
                (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (zipWith fullSub xs ys)
                i' <- runCircuit z
                j' <- runCircuit w
                s' <- newAssigned (\v -> v i' - v j' + v b - one)
                _ <- expansion (highRegisterSize @a @n) s'
                return (s' : k : zs)

            fullSub :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullSub xk yk b = do
                i <- runCircuit xk
                j <- runCircuit yk
                s <- newAssigned (\v -> v i - v j + v b + t `scale` one)
                splitExpansion (registerSize @a @n) 1 s

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    UInt _ _ - UInt _ _ = error "UInt: unreachable"

    negate (UInt xs x) = UInt (map forceZero xs) (forceZero x)
        where
            forceZero r = circuit $ do
                i <- runCircuit r
                constraint ($ i)
                return i

instance (Arithmetic a, KnownNat n) => MultiplicativeSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt [] x * UInt [] y = UInt [] $ circuit $ do
        z <- runCircuit (x * y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

    UInt (x : xs) z * UInt (y : ys) w =
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                is <- for xs runCircuit
                js <- for ys runCircuit
                i' <- runCircuit z
                j' <- runCircuit w
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @a @n
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r - 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k - l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @a @n) (registerSize @a @n) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n) (maxOverflow @a @n) s
                -- high register
                p' <- foldrM (\k l -> newAssigned (\v -> v l + v (cs ! k) * v (ds ! (r - 1 - k)))) c' [0 .. r - 1]
                _ <- expansion (highRegisterSize @a @n) p'
                -- all addends higher should be zero
                for_ [r .. r * 2 - 2] $ \k ->
                    for_ [k - r + 1 .. r - 1] $ \l ->
                        constraint (\v -> v (cs ! l) * v (ds ! (k - l)))
                return (p' : p : ps)

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    UInt _ _ * UInt _ _ = error "UInt: unreachable"

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (UInt n (ArithmeticCircuit a)) where
    one | numberOfRegisters @a @n Haskell.== 1 = UInt [] one
        | otherwise = UInt (one : replicate (numberOfRegisters @a @n - 2) zero) zero

--------------------------------------------------------------------------------

maxOverflow :: forall a n . (Finite a, KnownNat n) => Integer
maxOverflow = registerSize @a @n + Haskell.ceiling (log2 $ numberOfRegisters @a @n)

highRegisterSize :: forall a n . (Finite a, KnownNat n) => Integer
highRegisterSize = getInteger @n - registerSize @a @n * (numberOfRegisters @a @n - 1)

registerSize :: forall a n . (Finite a, KnownNat n) => Integer
registerSize = Haskell.ceiling (getInteger @n % numberOfRegisters @a @n)

numberOfRegisters :: forall a n . (Finite a, KnownNat n) => Integer
numberOfRegisters = fromMaybe (error "too many bits, field is not big enough")
    $ find (\c -> c * maxRegisterSize c Haskell.>= getInteger @n) [1 .. maxRegisterCount]
    where
        maxRegisterCount = 2 ^ bitLimit
        bitLimit = Haskell.floor $ log2 (order @a)
        maxRegisterSize regCount =
            let maxAdded = Haskell.ceiling $ log2 regCount
             in Haskell.floor $ (bitLimit - maxAdded) % (2 :: Integer)

log2 :: Integer -> Haskell.Double
log2 = Haskell.logBase 2 . Haskell.fromInteger

getInteger :: forall n . KnownNat n => Integer
getInteger = Haskell.fromIntegral $ natVal (Proxy :: Proxy n)
