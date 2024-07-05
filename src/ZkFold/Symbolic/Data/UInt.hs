{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE NoDeriveAnyClass     #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Data.UInt (
    StrictConv(..),
    StrictNum(..),
    UInt(..),
    toConstant,
    eea
) where

import           Control.DeepSeq
import           Control.Monad.State                                       (StateT (..))
import           Data.Foldable                                             (foldr, foldrM, for_)
import           Data.Functor                                              ((<$>))
import           Data.Kind                                                 (Type)
import           Data.List                                                 (unfoldr, zip)
import           Data.Map                                                  (fromList, (!))
import           Data.Traversable                                          (for, traverse)
import           Data.Tuple                                                (swap)
import qualified Data.Zip                                                  as Z
import           GHC.Generics                                              (Generic)
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (Natural)
import           Prelude                                                   (Integer, error, flip, otherwise, return,
                                                                            type (~), ($), (++), (.), (<>), (>>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (drop, length, replicate, replicateA)
import           ZkFold.Symbolic.Compiler                                  hiding (forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedV, expansion, joinCircuits,
                                                                            splitExpansion)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.FieldElement                         (FieldElementData (..))
import           ZkFold.Symbolic.Data.Ord

-- TODO (Issue #18): hide this constructor
--data family UInt :: Natural -> Type -> Type

newtype UInt (n :: Natural) (backend :: Natural -> Type -> Type) (a :: Type) = UInt (backend (NumberOfRegisters a n) a)

deriving instance Generic (UInt n backend a)
deriving instance (NFData (backend (NumberOfRegisters a n) a)) => NFData (UInt n backend a)
deriving instance (Haskell.Eq (backend (NumberOfRegisters a n) a)) => Haskell.Eq (UInt n backend a)
deriving instance (Haskell.Show a, Haskell.Show (backend (NumberOfRegisters a n) a)) => Haskell.Show (UInt n backend a)
deriving newtype instance Arithmetic a => Arithmetizable a (UInt n ArithmeticCircuit a)

instance Arithmetic a => FieldElementData a Vector (UInt n Vector a) where
    type TypeSize a Vector (UInt n Vector a) = NumberOfRegisters a n

    toFieldElements (UInt c) = c

    fromFieldElements = UInt

instance (KnownNat n, Finite (Zp p)) => FromConstant Natural (UInt n Vector (Zp p)) where
    fromConstant c =
        let (lo, hi, _) = cast @(Zp p) @n . (`Haskell.mod` (2 ^ getNatural @n)) $ c
         in UInt $ V.unsafeToVector $ (fromConstant <$> lo) <> [fromConstant hi]

instance (KnownNat n, Finite (Zp p)) => FromConstant Integer (UInt n Vector (Zp p)) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance
    ( FromConstant Natural a
    , Arithmetic a
    , KnownNat n
    ) => FromConstant Natural (UInt n ArithmeticCircuit a) where
    fromConstant c =
        let (lo, hi, _) = cast @a @n . (`Haskell.mod` (2 ^ getNatural @n)) $ c
         in UInt $ embedV $ Vector $ fromConstant <$> (lo <> [hi])

instance
    ( FromConstant Natural a
    , Arithmetic a
    , KnownNat n
    ) => FromConstant Integer (UInt n ArithmeticCircuit a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural (UInt n b a), Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n b a)) => Scale Natural (UInt n b a)

instance (FromConstant Integer (UInt n b a), Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n b a)) => Scale Integer (UInt n b a)

instance MultiplicativeMonoid (UInt n b a) => Exponent (UInt n b a) Natural where
    (^) = natPow

cast :: forall a n . (Finite a, KnownNat n) => Natural -> ([Natural], Natural, [Natural])
cast n =
    let base = 2 ^ registerSize @a @n
        registers = flip unfoldr n $ \case
            0 -> Haskell.Nothing
            x -> Haskell.Just (swap $ x `Haskell.divMod` base)
        r = numberOfRegisters @a @n -! 1
     in case greedySplitAt r registers of
        (lo, hi:rest) -> (lo, hi, rest)
        (lo, [])      -> ((lo ++ replicate (r -! length lo) zero), zero, [])
    where
        greedySplitAt 0 xs = ([], xs)
        greedySplitAt _ [] = ([], [])
        greedySplitAt m (x : xs) =
            let (ys, zs) = greedySplitAt (m -! 1) xs
             in (x : ys, zs)

-- | Extended Euclidean algorithm.
-- Exploits the fact that @s_i@ and @t_i@ change signs in turns on each iteration, so it adjusts the formulas correspondingly
-- and never requires signed arithmetic.
-- (i.e. it calculates @x = b - a@ instead of @x = a - b@ when @a - b@ is negative
-- and changes @y - x@ to @y + x@ on the following iteration)
-- This only affects Bezout coefficients, remainders are calculated without changes as they are always non-negative.
--
-- If the algorithm is used to calculate Bezout coefficients,
-- it requires that @a@ and @b@ are coprime, @b@ is not 1 and @a@ is not 0, otherwise the optimisation above is not valid.
--
-- If the algorithm is only used to find @gcd(a, b)@ (i.e. @s@ and @t@ will be discarded), @a@ and @b@ can be arbitrary integers.
--
eea
    :: forall n b a
    .  EuclideanDomain (UInt n b a)
    => KnownNat n
    => AdditiveGroup (UInt n b a)
    => Eq (Bool (b 1 a)) (UInt n b a)
    => Conditional (Bool (b 1 a)) (UInt n b a, UInt n b a, UInt n b a)
    => UInt n b a -> UInt n b a -> (UInt n b a, UInt n b a, UInt n b a)
eea a b = eea' 1 a b one zero zero one
    where
        iterations :: Natural
        iterations = value @n * 2 + 1

        eea' :: Natural -> UInt n b a -> UInt n b a -> UInt n b a -> UInt n b a -> UInt n b a -> UInt n b a -> (UInt n b a, UInt n b a, UInt n b a)
        eea' iteration oldR r oldS s oldT t
          | iteration == iterations = (oldS, oldT, oldR)
          | otherwise = bool @(Bool (b 1 a)) rec (if Haskell.even iteration then b - oldS else oldS, if Haskell.odd iteration then a - oldT else oldT, oldR) (r == zero)
            where
                quotient = oldR `div` r

                rec = eea' (iteration + 1) r (oldR - quotient * r) s (quotient * s + oldS) t (quotient * t + oldT)

--------------------------------------------------------------------------------

instance (Finite (Zp p), KnownNat n, KnownNat m, n <= m) => Extend (UInt n Vector (Zp p)) (UInt m Vector (Zp p)) where
    extend = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownNat m, m <= n) => Shrink (UInt n Vector (Zp p)) (UInt m Vector (Zp p)) where
    shrink = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n) => Eq (Bool (Vector 1 (Zp p))) (UInt n Vector (Zp p)) where
    x == y = Bool . V.singleton . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.== toConstant y
    x /= y = Bool . V.singleton . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell./= toConstant y

instance (Finite (Zp p), KnownNat n) => Ord (Bool (Vector 1 (Zp p))) (UInt n Vector (Zp p)) where
    x <= y = Bool . V.singleton . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.<= toConstant y
    x < y  = Bool . V.singleton . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.< toConstant y
    x >= y = Bool . V.singleton . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.>= toConstant y
    x > y  = Bool . V.singleton . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.> toConstant y
    max x y = fromConstant $ Haskell.max (toConstant @_ @Natural x) (toConstant y)
    min x y = fromConstant $ Haskell.min (toConstant @_ @Natural x) (toConstant y)

instance (Finite (Zp p), KnownNat n) => ToConstant (UInt n Vector (Zp p)) Natural where
    toConstant (UInt xs) = foldr (\p y -> fromZp p + base * y) 0 xs
        where base = 2 ^ registerSize @(Zp p) @n

instance (Finite (Zp p), KnownNat n) => ToConstant (UInt n Vector (Zp p)) Integer where
    toConstant = Haskell.fromIntegral @Natural . toConstant

instance (Finite (Zp p), KnownNat n) => AdditiveSemigroup (UInt n Vector (Zp p)) where
    x + y = fromConstant $ toConstant x + toConstant @_ @Natural y

instance (Finite (Zp p), KnownNat n) => AdditiveMonoid (UInt n Vector (Zp p)) where
    zero = fromConstant (0 :: Natural)

instance (Finite (Zp p), KnownNat n) => AdditiveGroup (UInt n Vector (Zp p)) where
    x - y = fromConstant $ toConstant x + 2 ^ getNatural @n -! toConstant y
    negate x = fromConstant $ 2 ^ getNatural @n -! toConstant x

instance (Finite (Zp p), KnownNat n) => MultiplicativeSemigroup (UInt n Vector (Zp p)) where
    x * y = fromConstant $ toConstant x * toConstant @_ @Natural y

instance (Finite (Zp p), KnownNat n) => MultiplicativeMonoid (UInt n Vector (Zp p)) where
    one = fromConstant (1 :: Natural)

instance (Finite (Zp p), KnownNat n) => Semiring (UInt n Vector (Zp p))

instance (Finite (Zp p), KnownNat n) => Ring (UInt n Vector (Zp p))

instance (Finite (Zp p), KnownNat n) => Arbitrary (UInt n Vector (Zp p)) where
    arbitrary = do
        lo <- replicateA (numberOfRegisters @(Zp p) @n -! 1) (toss $ registerSize @(Zp p) @n)
        hi <- toss (highRegisterSize @(Zp p) @n)
        return $ UInt $ V.unsafeToVector (lo <> [hi])
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Finite (Zp p), KnownNat n) => Iso (ByteString n Vector (Zp p)) (UInt n Vector (Zp p)) where
    from bs = fromConstant @Natural . toConstant $ bs

instance (Finite (Zp p), KnownNat n) => Iso (UInt n Vector (Zp p)) (ByteString n Vector (Zp p)) where
    from ui = fromConstant @Natural . toConstant $ ui


--------------------------------------------------------------------------------

instance Arithmetic a => SymbolicData a (UInt n ArithmeticCircuit a) where
    type TypeSize a (UInt n ArithmeticCircuit a) = NumberOfRegisters a n

    pieces (UInt c) = c

    restore c o = UInt $ c `withOutputs` o


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat k
    , n <= k
    , from ~ NumberOfRegisters a n
    , to ~ NumberOfRegisters a k
    ) => Extend (UInt n ArithmeticCircuit a) (UInt k ArithmeticCircuit a) where
    extend (UInt ac) = UInt (circuitN solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m (Vector to i)
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @a @n) (registerSize @a @n)
                zeros <- replicateA (value @k -! (value @n)) (newAssigned (Haskell.const zero))
                extended <- fromBits (highRegisterSize @a @k) (registerSize @a @k) (zeros <> bsBits)
                return $ V.unsafeToVector $ Haskell.reverse extended

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat k
    , k <= n
    , from ~ NumberOfRegisters a n
    , to ~ NumberOfRegisters a k
    ) => Shrink (UInt n ArithmeticCircuit a) (UInt k ArithmeticCircuit a) where
    shrink (UInt ac) = UInt (circuitN solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m (Vector to i)
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @a @n) (registerSize @a @n)
                shrinked <- fromBits (highRegisterSize @a @k) (registerSize @a @k) (drop (value @n -! (value @k)) bsBits)
                return $ V.unsafeToVector $ Haskell.reverse shrinked

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat r
    , KnownNat (r - 1)
    , KnownNat (r + r)
    , r ~ NumberOfRegisters a n
    , Ord (Bool (b 1 a)) (UInt n b a)
    , AdditiveGroup (UInt n b a)
    , Semiring (UInt n b a)
    , MultiplicativeMonoid (UInt n b a)
    , FromConstant Natural (UInt n b a)
    , BitState ByteString n b a
    , Iso (ByteString n b a) (UInt n b a)
    , Eq (Bool (b 1 a)) (UInt n b a)
    , Conditional (Bool (b 1 a)) (UInt n b a)
    , Conditional (Bool (b 1 a)) (UInt n b a, UInt n b a)
    , 1 + (r - 1) ~ r
    , 1 <= r
    ) => EuclideanDomain (UInt n b a) where
    divMod numerator d = bool @(Bool (b 1 a)) (q, r) (zero, zero) (d == zero)
        where
            (q, r) = Haskell.foldl longDivisionStep (zero, zero) [value @n -! 1, value @n -! 2 .. 0]

            numeratorBits :: ByteString n b a
            numeratorBits = from numerator

            addBit :: UInt n b a -> Natural -> UInt n b a
            addBit ui bs = ui + (bool @(Bool (b 1 a)) zero one (isSet numeratorBits bs))

            longDivisionStep
                :: (UInt n b a, UInt n b a)
                -> Natural
                -> (UInt n b a, UInt n b a)
            longDivisionStep (q', r') i =
                let rs = addBit (r' + r') (value @n -! i -! 1)
                 in bool @(Bool (b 1 a)) (q', rs) (q' + fromConstant ((2 :: Natural) ^ i), rs - d) (rs >= d)

instance (Arithmetic a, KnownNat n, KnownNat (NumberOfRegisters a n)) => Ord (Bool (ArithmeticCircuit 1 a)) (UInt n ArithmeticCircuit a) where
    x <= y = y >= x

    x <  y = y > x

    u1 >= u2 =
        let ByteString rs1 = from u1 :: ByteString n ArithmeticCircuit a
            ByteString rs2 = from u2 :: ByteString n ArithmeticCircuit a
         in circuitGE rs1 rs2

    u1 > u2 =
        let ByteString rs1 = from u1 :: ByteString n ArithmeticCircuit a
            ByteString rs2 = from u2 :: ByteString n ArithmeticCircuit a
         in circuitGT rs1 rs2

    max x y = bool @(Bool (ArithmeticCircuit 1 a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit 1 a)) x y $ x > y


instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (UInt n ArithmeticCircuit a) where
    UInt x + UInt y = UInt (circuitN solve)
        where
            solve :: MonadBlueprint i a m => m (Vector (NumberOfRegisters a n) i)
            solve = do
                xs <- runCircuit x
                ys <- runCircuit y
                z <- newAssigned (Haskell.const zero)
                (zs, _) <- flip runStateT z $ traverse StateT $
                    Z.zipWith (fullAdder $ registerSize @a @n) xs ys
                return zs

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n)
    ) => AdditiveMonoid (UInt n ArithmeticCircuit a) where
    zero = UInt zero

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n)
    ) => AdditiveGroup (UInt n ArithmeticCircuit a) where

        UInt x - UInt y = UInt $ circuitN (V.unsafeToVector <$> solve)
            where
                t :: a
                t = (one + one) ^ registerSize @a @n - one

                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    is <- runCircuit x
                    js <- runCircuit y
                    case V.fromVector $ Z.zip is js of
                      []              -> return []
                      [(i, j)]        -> solve1 i j
                      ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                             (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                          in solveN (i, j) (ris, rjs) (z, w)

                solve1 :: MonadBlueprint i a m => i -> i -> m [i]
                solve1 i j = do
                    z0 <- newAssigned (\v -> v i - v j + fromConstant (2 ^ registerSize @a @n :: Natural))
                    (z, _) <- splitExpansion (highRegisterSize @a @n) 1 z0
                    return [z]

                solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
                solveN (i, j) (is, js) (i', j') = do
                    s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                    (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                    (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                    d <- newAssigned (\v -> v i' - v j')
                    s'0 <- newAssigned (\v -> v d + v b + fromConstant t)
                    (s', _) <- splitExpansion (highRegisterSize @a @n) 1 s'0
                    return (k : zs <> [s'])

                fullSub :: MonadBlueprint i a m => i -> i -> i -> m (i, i)
                fullSub xk yk b = do
                    d <- newAssigned (\v -> v xk - v yk)
                    s <- newAssigned (\v -> v d + v b + fromConstant t)
                    splitExpansion (registerSize @a @n) 1 s

        negate (UInt x) =
            let y = 2 ^ registerSize @a @n
                ys = replicate (numberOfRegisters @a @n -! 2) (2 ^ registerSize @a @n -! 1)
                y' = 2 ^ highRegisterSize @a @n -! 1
                ns
                  | numberOfRegisters @a @n == 1 = V.unsafeToVector [y' + 1]
                  | otherwise = V.unsafeToVector $ (y : ys) <> [y']
             in UInt (negateN ns x)

negateN :: forall a n . Arithmetic a => Vector n Natural -> ArithmeticCircuit n a -> ArithmeticCircuit n a
negateN ns r = circuitN $ do
    is <- runCircuit r
    for (Z.zip is ns) $ \(i, n) -> newAssigned (\v -> fromConstant n - v i)

instance (Arithmetic a, KnownNat n, r ~ NumberOfRegisters a n) => MultiplicativeSemigroup (UInt n ArithmeticCircuit a) where
    UInt x * UInt y = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            solve :: MonadBlueprint i a m => m [i]
            solve = do
                is <- runCircuit x
                js <- runCircuit y
                case V.fromVector $ Z.zip is js of
                  []              -> return []
                  [(i, j)]        -> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadBlueprint i a m => i -> i -> m [i]
            solve1 i j = do
                (z, _) <- newAssigned (\v -> v i * v j) >>= splitExpansion (highRegisterSize @a @n) (maxOverflow @a @n)
                return [z]

            solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @a @n
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @a @n) (registerSize @a @n) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n) (maxOverflow @a @n) s
                -- high register
                p'0 <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v k' + v l)) c' [0 .. r -! 1]
                (p', _) <- splitExpansion (highRegisterSize @a @n) (maxOverflow @a @n) p'0
                return (p : ps <> [p'])


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n)
    , KnownNat (NumberOfRegisters a n - 1)
    , 1 + (NumberOfRegisters a n - 1) ~ NumberOfRegisters a n
    ) => MultiplicativeMonoid (UInt n ArithmeticCircuit a) where

    one = UInt $ (one :: ArithmeticCircuit 1 a) `joinCircuits` (zero :: ArithmeticCircuit (NumberOfRegisters a n - 1) a)


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n)
    , KnownNat (NumberOfRegisters a n - 1)
    , 1 + (NumberOfRegisters a n - 1) ~ NumberOfRegisters a n
    ) => Semiring (UInt n ArithmeticCircuit a)

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n)
    , KnownNat (NumberOfRegisters a n - 1)
    , 1 + (NumberOfRegisters a n - 1) ~ NumberOfRegisters a n
    ) => Ring (UInt n ArithmeticCircuit a)

deriving via (Structural (UInt n ArithmeticCircuit a))
         instance (Arithmetic a, KnownNat r, r ~ NumberOfRegisters a n, 1 <= r) =>
         Eq (Bool (ArithmeticCircuit 1 a)) (UInt n ArithmeticCircuit a)

instance (Arithmetic a, KnownNat n) => Arbitrary (UInt n ArithmeticCircuit a) where
    arbitrary = do
        lows <- replicateA (numberOfRegisters @a @n -! 1) (toss $ registerSize @a @n)
        hi <- toss (highRegisterSize @a @n)
        return $ UInt $ embedV (V.unsafeToVector $ lows <> [hi])
        where
            toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Arithmetic a, KnownNat n) => Iso (ByteString n ArithmeticCircuit a) (UInt n ArithmeticCircuit a) where
    from (ByteString bits) = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- V.fromVector <$> runCircuit bits
                Haskell.reverse <$> fromBits (highRegisterSize @a @n) (registerSize @a @n) bsBits

instance (Arithmetic a, KnownNat n) => Iso (UInt n ArithmeticCircuit a) (ByteString n ArithmeticCircuit a) where
    from (UInt ac) = ByteString $ circuitN $ Vector <$> solve
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                toBits (Haskell.reverse regs) (highRegisterSize @a @n) (registerSize @a @n)


--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (Finite (Zp p), KnownNat n) => StrictConv Natural (UInt n Vector (Zp p)) where
    strictConv n = case cast @(Zp p) @n n of
        (lo, hi, []) -> UInt $ V.unsafeToVector $ (toZp . Haskell.fromIntegral <$> lo) <> [toZp . Haskell.fromIntegral $ hi]
        _            -> error "strictConv: overflow"

instance (FromConstant Natural a, Arithmetic a, KnownNat n, r ~ NumberOfRegisters a n) => StrictConv Natural (UInt n ArithmeticCircuit a) where
    strictConv n = case cast @a @n n of
        (lo, hi, []) -> UInt $ embedV $ V.unsafeToVector $ fromConstant <$> (lo <> [hi])
        _            -> error "strictConv: overflow"

instance (Finite (Zp p), KnownNat n) => StrictConv (Zp p) (UInt n Vector (Zp p)) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Finite (Zp p), Prime p, KnownNat n) => StrictConv (Zp p) (UInt n ArithmeticCircuit (Zp p)) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Arithmetic a, KnownNat n, NumberOfBits a <= n) => StrictConv (ArithmeticCircuit 1 a) (UInt n ArithmeticCircuit a) where
    strictConv a = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            requiredBits :: Natural
            requiredBits = (numberOfRegisters @a @n -! 1) * (registerSize @a @n) + (highRegisterSize @a @n)

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- V.item <$> runCircuit a
                bits <- Haskell.reverse <$> expansion requiredBits i
                fromBits (highRegisterSize @a @n) (registerSize @a @n) bits


class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Finite (Zp p), KnownNat n) => StrictNum (UInt n Vector (Zp p)) where
    strictAdd x y = strictConv $ toConstant x + toConstant @_ @Natural y
    strictSub x y = strictConv $ toConstant x -! toConstant y
    strictMul x y = strictConv $ toConstant x * toConstant @_ @Natural y

instance (Arithmetic a, KnownNat n) => StrictNum (UInt n ArithmeticCircuit a) where
    strictAdd (UInt x) (UInt y) = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            solve :: MonadBlueprint i a m => m [i]
            solve = do
                j <- newAssigned (Haskell.const zero)
                xs <- V.fromVector <$> runCircuit x
                ys <- V.fromVector <$> runCircuit y
                let midx = Haskell.init xs
                    z    = Haskell.last xs
                    midy = Haskell.init ys
                    w    = Haskell.last ys
                (zs, c) <- flip runStateT j $ traverse StateT $
                    Haskell.zipWith (fullAdder $ registerSize @a @n) midx midy
                k <- fullAdded z w c
                _ <- expansion (highRegisterSize @a @n) k
                return (zs <> [k])


    strictSub (UInt x) (UInt y) = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                is <- runCircuit x
                js <- runCircuit y
                case V.fromVector $ Z.zip is js of
                  []              -> return []
                  [(i, j)]        -> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadBlueprint i a m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned (\v -> v i - v j)
                _ <- expansion (highRegisterSize @a @n) z
                return [z]

            solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                k' <- newAssigned (\v -> v i' - v j')
                s' <- newAssigned (\v -> v k' + v b - one)
                _ <- expansion (highRegisterSize @a @n) s'
                return (k : zs <> [s'])


            fullSub :: MonadBlueprint i a m => i -> i -> i -> m (i, i)
            fullSub xk yk b = do
                k <- newAssigned (\v -> v xk - v yk)
                s <- newAssigned (\v -> v k + v b + fromConstant t)
                splitExpansion (registerSize @a @n) 1 s

    strictMul (UInt x) (UInt y) = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            solve :: MonadBlueprint i a m => m [i]
            solve = do
                is <- runCircuit x
                js <- runCircuit y
                case V.fromVector $ Z.zip is js of
                  []              -> return []
                  [(i, j)]        -> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadBlueprint i a m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned $ \v -> v i * v j
                _ <- expansion (highRegisterSize @a @n) z
                return [z]

            solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @a @n
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @a @n) (registerSize @a @n) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n) (maxOverflow @a @n) s
                -- high register
                p' <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v l + v k')) c' [0 .. r -! 1]
                _ <- expansion (highRegisterSize @a @n) p'
                -- all addends higher should be zero
                for_ [r .. r * 2 -! 2] $ \k ->
                    for_ [k -! r + 1 .. r -! 1] $ \l ->
                        constraint (\v -> v (cs ! l) * v (ds ! (k -! l)))
                return (p : ps <> [p'])


--------------------------------------------------------------------------------

fullAdder :: MonadBlueprint i a m => Natural -> i -> i -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadBlueprint i a m => i -> i -> i -> m i
fullAdded i j c = do
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)
