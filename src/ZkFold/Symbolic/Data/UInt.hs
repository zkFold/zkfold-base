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

import           Control.Applicative                                       (pure)
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
import           GHC.Generics                                              (Generic, Par1 (..))
import           Prelude                                                   (Integer, error, flip, otherwise, return,
                                                                            type (~), ($), (++), (.), (<>), (>>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Control.HApplicative                          (hliftA2)
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (drop, length, replicate, replicateA)
import           ZkFold.Symbolic.Class                                    
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedV, expansion, splitExpansion)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class                                (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Interpreter                               (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit                              (constraint, newAssigned, MonadCircuit)

-- TODO (Issue #18): hide this constructor
newtype UInt (n :: Natural) (r :: RegisterSize) (context :: (Type -> Type) -> Type) = UInt (context (Vector (NumberOfRegisters (BaseField context) n r)))

deriving instance Generic (UInt n r context)
deriving instance (NFData (context (Vector (NumberOfRegisters (BaseField context) n r)))) => NFData (UInt n r context)
deriving instance (Haskell.Eq (context (Vector (NumberOfRegisters (BaseField context) n r)))) => Haskell.Eq (UInt n r context)
deriving instance (Haskell.Show (BaseField context), Haskell.Show (context (Vector (NumberOfRegisters (BaseField context) n r)))) => Haskell.Show (UInt n r context)
deriving newtype instance SymbolicData c (UInt n r c)

instance (FromConstant a Natural, FromConstant Natural a, Symbolic c) => FromConstant a (UInt n r c) where
    fromConstant c =
        let c' = toConstant . (fromConstant :: a -> Natural) $ c
            (lo, hi, _) = cast @(BaseField c) @n @r . (`Haskell.mod` (2 ^ getNatural @n)) $ c'
        in UInt . embed @c $ V.unsafeToVector $ (fromConstant <$> lo) <> [fromConstant hi]

-- instance
--     ( FromConstant Natural a
--     , Arithmetic a
--     , KnownNat n
--     , KnownRegisterSize r
--     ) => FromConstant Natural (UInt n r (ArithmeticCircuit a)) where
--     fromConstant c =
--         let (lo, hi, _) = cast @a @n @r . (`Haskell.mod` (2 ^ getNatural @n)) $ c
--          in UInt $ embedV $ Vector $ fromConstant <$> (lo <> [hi])

-- instance (KnownNat n, Finite (Zp p), KnownRegisterSize r) => FromConstant Integer (UInt n r (Interpreter (Zp p))) where
--     fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))
-- instance
--     ( FromConstant Natural a
--     , Arithmetic a
--     , KnownNat n
--     , KnownRegisterSize r
--     ) => FromConstant Integer (UInt n r (ArithmeticCircuit a)) where
--     fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Arithmetic a, FromConstant a (UInt n r c), MultiplicativeSemigroup (UInt n r c)) => Scale a (UInt n r c)

-- instance (FromConstant Integer (UInt n r c), KnownNat n, MultiplicativeSemigroup (UInt n r c)) => Scale Integer (UInt n r c)

instance MultiplicativeMonoid (UInt n r c) => Exponent (UInt n r c) Natural where
    (^) = natPow

cast :: forall a n r . (Finite a, KnownNat n, KnownRegisterSize r) => Natural -> ([Natural], Natural, [Natural])
cast n =
    let base = 2 ^ registerSize @a @n @r
        registers = flip unfoldr n $ \case
            0 -> Haskell.Nothing
            x -> Haskell.Just (swap $ x `Haskell.divMod` base)
        r = numberOfRegisters @a @n @r -! 1
     in case greedySplitAt r registers of
        (lo, hi:rest) -> (lo, hi, rest)
        (lo, [])      -> (lo ++ replicate (r -! length lo) zero, zero, [])
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
    :: forall n c r
    .  Symbolic c
    => EuclideanDomain (UInt n r c)
    => KnownNat n
    => KnownNat (NumberOfRegisters (BaseField c) n r)
    => AdditiveGroup (UInt n r c)
    => Eq (Bool c) (UInt n r c)
    => UInt n r c -> UInt n r c -> (UInt n r c, UInt n r c, UInt n r c)
eea a b = eea' 1 a b one zero zero one
    where
        iterations :: Natural
        iterations = value @n * 2 + 1

        eea' :: Natural -> UInt n r c -> UInt n r c -> UInt n r c -> UInt n r c -> UInt n r c -> UInt n r c -> (UInt n r c, UInt n r c, UInt n r c)
        eea' iteration oldR r oldS s oldT t
          | iteration Haskell.== iterations = (oldS, oldT, oldR)
          | otherwise = bool @(Bool c) rec (if Haskell.even iteration then b - oldS else oldS, if Haskell.odd iteration then a - oldT else oldT, oldR) (r == zero)
            where
                quotient = oldR `div` r

                rec = eea' (iteration + 1) r (oldR - quotient * r) s (quotient * s + oldS) t (quotient * t + oldT)

--------------------------------------------------------------------------------

-- instance (Symbolic c, Prime p) => Extend (UInt n r (Interpreter (Zp p))) (UInt m r (Interpreter (Zp p))) where
--     extend = fromConstant @Natural . toConstant

-- instance (Symbolic c, Prime p) => Shrink (UInt n r (Interpreter (Zp p))) (UInt m r (Interpreter (Zp p))) where
--     shrink = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Eq (Bool (Interpreter (Zp p))) (UInt n r (Interpreter (Zp p))) where
    x == y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.== toConstant y
    x /= y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell./= toConstant y

instance (Prime p, KnownNat n, KnownRegisterSize r) => Ord (Bool (Interpreter (Zp p))) (UInt n r (Interpreter (Zp p))) where
    x <= y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.<= toConstant y
    x < y  = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.< toConstant y
    x >= y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.>= toConstant y
    x > y  = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.> toConstant y
    max x y = fromConstant $ Haskell.max (toConstant @_ @Natural x) (toConstant y)
    min x y = fromConstant $ Haskell.min (toConstant @_ @Natural x) (toConstant y)

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter (Zp p))) a where
    toConstant (UInt (Interpreter xs)) =  Haskell.fromIntegral @Natural $ foldr (\p y -> fromZp p + base * y) 0 xs
        where base = 2 ^ registerSize @(Zp p) @n @r

instance (Prime p, KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter (Zp p))) Integer where
    toConstant = Haskell.fromIntegral @Natural . toConstant

-- instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => AdditiveSemigroup (UInt n r (Interpreter (Zp p))) where
--     x + y = fromConstant $ toConstant x + toConstant @_ @Natural y

-- instance (Symbolic c, KnownNat (NumberOfRegisters (BaseField c) n r), KnownRegisterSize r) => AdditiveMonoid (UInt n r c) where
--     zero = UInt $ fromConstant (0 :: Natural)

-- instance (Prime p, KnownNat n, KnownRegisterSize r) => AdditiveGroup (UInt n r (Interpreter (Zp p))) where
    -- x - y = fromConstant $ toConstant x + 2 ^ getNatural @n -! toConstant y
    -- negate x = fromConstant $ 2 ^ getNatural @n -! toConstant x

-- instance (Prime p, KnownNat n, KnownRegisterSize r) => MultiplicativeSemigroup (UInt n r (Interpreter (Zp p))) where
--     x * y = fromConstant $ toConstant x * toConstant @_ @Natural y

instance (KnownNat n,  KnownRegisterSize r, Symbolic c) => MultiplicativeMonoid (UInt n r c) where
    one = fromConstant (1 :: Natural)

instance (Prime p, KnownNat n, KnownRegisterSize r) => Semiring (UInt n r (Interpreter (Zp p)))

instance (Prime p, KnownNat n, KnownRegisterSize r) => Ring (UInt n r (Interpreter (Zp p)))

instance (KnownNat n, Symbolic c, KnownRegisterSize r) => Arbitrary (UInt n r c) where
    arbitrary = do
        lo <- replicateA (numberOfRegisters @(BaseField c) @n @r -! 1) (toss $ registerSize @(BaseField c) @n @r)
        hi <- toss (highRegisterSize @(BaseField c) @n @r)
        return $ UInt $ embed $ V.unsafeToVector (lo <> [hi])
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Arithmetic (Zp p), KnownNat n, KnownRegisterSize r) => Iso (ByteString n (Interpreter (Zp p))) (UInt n r (Interpreter (Zp p))) where
    from = fromConstant @Natural . toConstant

instance (Arithmetic (Zp p), KnownNat n, KnownRegisterSize r) => Iso (UInt n r (Interpreter (Zp p))) (ByteString n (Interpreter (Zp p))) where
    from = fromConstant @Natural . toConstant

--------------------------------------------------------------------------------

instance
    ( Symbolic c
    , KnownNat n
    , KnownNat k
    , KnownRegisterSize r
    , n <= k
    , from ~ NumberOfRegisters (BaseField c) n r
    , to ~ NumberOfRegisters (BaseField c) k r
    , BaseField с ~ BaseField c
    ) => Extend (UInt n r с) (UInt k r с) where
    extend (UInt ac) = UInt $ symbolicF ac (V.unsafeToVector . V.fromVector ) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector from i -> m (Vector to i)
            solve xv = do
                let regs = V.fromVector xv
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r)
                zeros <- replicateA (value @k -! (value @n)) (newAssigned (Haskell.const zero))
                extended <- fromBits (highRegisterSize @(BaseField c) @k @r) (registerSize @(BaseField c) @k @r) (zeros <> bsBits)
                return $ V.unsafeToVector $ Haskell.reverse extended

instance
    ( Symbolic c
    , KnownNat n
    , KnownNat k
    , KnownRegisterSize r
    , k <= n
    , from ~ NumberOfRegisters (BaseField c) n r
    , to ~ NumberOfRegisters (BaseField c) k r
    , BaseField c ~ BaseField c
    ) => Shrink (UInt n r c) (UInt k r c) where
    shrink (UInt ac) =  UInt $ symbolicF ac (V.unsafeToVector . V.fromVector ) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector from i -> m (Vector to i)
            solve xv = do
                let regs = V.fromVector xv
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r)
                shrinked <- fromBits (highRegisterSize @(BaseField c) @k @r) (registerSize @(BaseField c) @k @r) (drop (value @n -! (value @k)) bsBits)
                return $ V.unsafeToVector $ Haskell.reverse shrinked

instance
    ( KnownNat n
    , KnownNat r
    , KnownNat (r - 1)
    , KnownNat (r + r)
    , KnownRegisterSize rs
    , r ~ NumberOfRegisters (BaseField c) n rs
    , Symbolic c
    , NFData (c (Vector r))
    , Ord (Bool c) (UInt n rs c)
    , AdditiveGroup (UInt n rs c)
    , Semiring (UInt n rs c)
    , MultiplicativeMonoid (UInt n rs c)
    , FromConstant Natural (UInt n rs c)
    , BitState ByteString n c
    , Iso (ByteString n c) (UInt n rs c)
    , Eq (Bool c) (UInt n rs c)
    , 1 + (r - 1) ~ r
    , 1 <= r
    ) => EuclideanDomain (UInt n rs c) where
    divMod numerator d = bool @(Bool c) (q, r) (zero, zero) (d == zero)
        where
            (q, r) = Haskell.foldl longDivisionStep (zero, zero) [value @n -! 1, value @n -! 2 .. 0]

            numeratorBits :: ByteString n c
            numeratorBits = from numerator

            addBit :: UInt n rs c -> Natural -> UInt n rs c
            addBit ui bs = ui + bool @(Bool c) zero one (isSet numeratorBits bs)

            longDivisionStep
                :: (UInt n rs c, UInt n rs c)
                -> Natural
                -> (UInt n rs c, UInt n rs c)
            longDivisionStep (q', r') i =
                let rs = force $ addBit (r' + r') (value @n -! i -! 1)
                 in bool @(Bool c) (q', rs) (q' + fromConstant ((2 :: Natural) ^ i), rs - d) (rs >= d)

instance (Arithmetic a, KnownNat n, KnownRegisterSize r, KnownNat (NumberOfRegisters a n r)) => Ord (Bool (ArithmeticCircuit a)) (UInt n r (ArithmeticCircuit a)) where
    x <= y = y >= x

    x <  y = y > x

    u1 >= u2 =
        let ByteString rs1 = from u1 :: ByteString n (ArithmeticCircuit a)
            ByteString rs2 = from u2 :: ByteString n (ArithmeticCircuit a)
         in bitwiseGE rs1 rs2

    u1 > u2 =
        let ByteString rs1 = from u1 :: ByteString n (ArithmeticCircuit a)
            ByteString rs2 = from u2 :: ByteString n (ArithmeticCircuit a)
         in bitwiseGT rs1 rs2

    max x y = bool @(Bool (ArithmeticCircuit a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit a)) x y $ x > y


instance (KnownNat n, KnownRegisterSize r, Symbolic c) => AdditiveSemigroup (UInt n r c) where
    UInt xc + UInt yc = UInt $ symbolic2F xc yc (\u v -> V.unsafeToVector $ V.fromVector u + V.fromVector v) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv yv = do
                j <- newAssigned (Haskell.const zero)
                let xs = V.fromVector xv
                    ys = V.fromVector yv
                    midx = Haskell.init xs
                    z    = Haskell.last xs
                    midy = Haskell.init ys
                    w    = Haskell.last ys
                (zs, c) <- flip runStateT j $ traverse StateT $
                    Haskell.zipWith (fullAdder $ registerSize @(BaseField c) @n @r) midx midy
                k <- fullAdded z w c
                (ks, _) <- splitExpansion (highRegisterSize @(BaseField c) @n @r) 1 k
                return $ V.unsafeToVector (zs ++ [ks])

instance
    ( Symbolic c
    , KnownNat (NumberOfRegisters (BaseField c) n r)
    , KnownRegisterSize r
    ) => AdditiveMonoid (UInt n r c) where
    zero = fromConstant (0:: Natural)

instance
    ( KnownNat n
    , KnownRegisterSize r
    , KnownNat (NumberOfRegisters (BaseField c) n r)
    , Symbolic c
    ) => AdditiveGroup (UInt n r c) where

    UInt x - UInt y = UInt $ symbolic2F x y (\u v -> V.unsafeToVector $ V.fromVector u + V.fromVector v) solve
        where
            t :: BaseField c
            t = (one + one) ^ registerSize @(BaseField c) @n @r - one

            solve :: forall i m. (MonadCircuit i (BaseField c) m) => Vector (NumberOfRegisters (BaseField c) n r) i -> Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv yv = do
                let is = V.fromVector xv
                    js = V.fromVector yv
                case Z.zip is js of
                    []              -> return $ V.unsafeToVector []
                    [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                    ((i, j) : rest) ->  let (z, w) = Haskell.last rest
                                            (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                        in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadCircuit i (BaseField c) m => i -> i -> m [i]
            solve1 i j = do
                z0 <- newAssigned (\v -> v i - v j + fromConstant (2 ^ registerSize @(BaseField c) @n @r :: Natural))
                (z, _) <- splitExpansion (highRegisterSize @(BaseField c) @n @r) 1 z0
                return [z]

            solveN :: MonadCircuit i (BaseField c) m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @(BaseField c) @n @r) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                d <- newAssigned (\v -> v i' - v j')
                s'0 <- newAssigned (\v -> v d + v b + fromConstant t)
                (s', _) <- splitExpansion (highRegisterSize @(BaseField c) @n @r) 1 s'0
                return (k : zs <> [s'])

            fullSub :: MonadCircuit i (BaseField c) m => i -> i -> i -> m (i, i)
            fullSub xk yk b = do
                d <- newAssigned (\v -> v xk - v yk)
                s <- newAssigned (\v -> v d + v b + fromConstant t)
                splitExpansion (registerSize @(BaseField c) @n @r) 1 s

    negate (UInt x) =  UInt $ symbolicF x negate solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv = do
                j <- newAssigned (Haskell.const zero)
                let xs = V.fromVector xv
                    y = 2 ^ registerSize @(BaseField c) @n @r
                    ys = replicate (numberOfRegisters @(BaseField c) @n @r -! 2) (2 ^ registerSize @(BaseField c) @n @r -! 1)
                    y' = 2 ^ highRegisterSize @(BaseField c) @n @r -! 1
                    ns
                        | numberOfRegisters @(BaseField c) @n @r Haskell.== 1 = [y' + 1]
                        | otherwise = (y : ys) <> [y']
                    (zs, _) = flip runStateT j $ traverse StateT (Haskell.zipWith negateN ns xs)
                return $ V.unsafeToVector zs

            negateN :: MonadCircuit i (BaseField c) m => Natural -> i -> i -> m (i, i)
            negateN n i b = do
                r <- newAssigned (\v -> fromConstant n - v i + v b)
                splitExpansion (registerSize @(BaseField c) @n @r) 1 r


instance (Arithmetic a, KnownNat n, KnownRegisterSize rs, r ~ NumberOfRegisters a n rs, Symbolic c) => MultiplicativeSemigroup (UInt n rs c) where
    UInt x * UInt y = UInt $ symbolic2F x y (\u v -> V.unsafeToVector $ V.fromVector u * V.fromVector v) solve
        where
            solve :: forall i m. (MonadCircuit i (BaseField c) m) => Vector (NumberOfRegisters (BaseField c) n rs) i -> Vector (NumberOfRegisters (BaseField c) n rs) i -> m (Vector (NumberOfRegisters (BaseField c) n rs) i)

            solve xv yv = do
                -- is <- runCircuit x
                -- js <- runCircuit y
                case V.fromVector $ Z.zip xv yv of
                  []              -> return $ V.unsafeToVector []
                  [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)

            solve1 :: forall i m. (MonadCircuit i (BaseField c) m) => i -> i -> m [i]
            solve1 i j = do
                (z, _) <- newAssigned (\v -> v i * v j) >>= splitExpansion (highRegisterSize @a @n @rs) (maxOverflow @a @n @rs)
                return [z]

            solveN :: forall i m. (MonadCircuit i (BaseField c) m) => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @a @n @rs
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @a @n @rs) (registerSize @a @n @rs) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n @rs) (maxOverflow @a @n @rs) s
                -- high register
                p'0 <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v k' + v l)) c' [0 .. r -! 1]
                (p', _) <- splitExpansion (highRegisterSize @a @n @rs) (maxOverflow @a @n @rs) p'0
                return (p : ps <> [p'])


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n r)
    , KnownNat (NumberOfRegisters a n r - 1)
    , KnownRegisterSize r
    , (NumberOfRegisters a n r - 1) + 1 ~ NumberOfRegisters a n r
    ) => MultiplicativeMonoid (UInt n r (ArithmeticCircuit a)) where

    one = UInt $ hliftA2 (\(Par1 h) t -> h V..: t) (embed one :: ArithmeticCircuit a Par1) (embedV (pure zero) :: ArithmeticCircuit a (Vector (NumberOfRegisters a n r - 1)))


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n r)
    , KnownNat (NumberOfRegisters a n r - 1)
    , KnownRegisterSize r
    , (NumberOfRegisters a n r - 1) + 1 ~ NumberOfRegisters a n r
    ) => Semiring (UInt n r (ArithmeticCircuit a))

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n r)
    , KnownNat (NumberOfRegisters a n r - 1)
    , KnownRegisterSize r
    , (NumberOfRegisters a n r - 1) + 1 ~ NumberOfRegisters a n r
    ) => Ring (UInt n r (ArithmeticCircuit a))

deriving via (Structural (UInt n rs (ArithmeticCircuit a)))
         instance (Arithmetic a, r ~ NumberOfRegisters a n rs, 1 <= r) =>
         Eq (Bool (ArithmeticCircuit a)) (UInt n rs (ArithmeticCircuit a))

instance ( KnownNat (NumberOfRegisters (BaseField c) n r)
        , KnownRegisterSize r
        , Symbolic c
        , KnownNat (NumberOfRegisters (BaseField c) n r) 
        ) => Iso (ByteString n c) (UInt n r c) where
    from (ByteString bits) = UInt $ symbolicF bits negate solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv = let bsBits = V.fromVector xv
                in V.unsafeToVector . Haskell.reverse <$> fromBits (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) bsBits

instance (Arithmetic a, KnownNat n, KnownRegisterSize r) => Iso (UInt n r (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where
    from (UInt ac) = ByteString $ circuitF $ Vector <$> solve
        where
            solve :: forall i m. MonadCircuit i a m => m [i]
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                toBits (Haskell.reverse regs) (highRegisterSize @a @n @r) (registerSize @a @n @r)


--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => StrictConv Natural (UInt n r (Interpreter (Zp p))) where
    strictConv n = case cast @(Zp p) @n @r n of
        (lo, hi, []) -> UInt $ Interpreter $ V.unsafeToVector $ (toZp . Haskell.fromIntegral <$> lo) <> [toZp . Haskell.fromIntegral $ hi]
        _            -> error "strictConv: overflow"

instance (FromConstant Natural a, Arithmetic a, KnownNat n, KnownRegisterSize rs, r ~ NumberOfRegisters a n rs) => StrictConv Natural (UInt n rs (ArithmeticCircuit a)) where
    strictConv n = case cast @a @n @rs n of
        (lo, hi, []) -> UInt $ embedV $ V.unsafeToVector $ fromConstant <$> (lo <> [hi])
        _            -> error "strictConv: overflow"

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => StrictConv (Zp p) (UInt n r (Interpreter (Zp p))) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Finite (Zp p), Prime p, KnownNat n, KnownRegisterSize r) => StrictConv (Zp p) (UInt n r (ArithmeticCircuit (Zp p))) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Arithmetic a, KnownNat n, KnownRegisterSize r, NumberOfBits a <= n) => StrictConv (ArithmeticCircuit a Par1) (UInt n r (ArithmeticCircuit a)) where
    strictConv a = UInt (circuitF $ V.unsafeToVector <$> solve)
        where
            solve :: MonadCircuit i a m => m [i]
            solve = do
                i <- unPar1 <$> runCircuit a
                let len = Haskell.min (getNatural @n) (numberOfBits @a)
                bits <- Haskell.reverse <$> expansion len i
                fromBits (highRegisterSize @a @n @r) (registerSize @a @n @r) bits


class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => StrictNum (UInt n r (Interpreter (Zp p))) where
    strictAdd x y = strictConv $ toConstant x + toConstant @_ @Natural y
    strictSub x y = strictConv $ toConstant x -! toConstant y
    strictMul x y = strictConv $ toConstant x * toConstant @_ @Natural y

instance (Arithmetic a, KnownNat n, KnownRegisterSize r, Symbolic c) => StrictNum (UInt n r c) where
    strictAdd (UInt x) (UInt y) = UInt $ symbolic2F x y (\u v -> V.unsafeToVector $ V.fromVector u + V.fromVector v) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv yv = do
                let j = newAssigned (Haskell.const zero)
                    xs = V.fromVector xv
                    ys = V.fromVector yv
                    midx = Haskell.init xs
                    z    = Haskell.last xs
                    midy = Haskell.init ys
                    w    = Haskell.last ys
                (zs, c) <- flip runStateT j $ traverse StateT $
                    Haskell.zipWith (fullAdder $ registerSize @(BaseField c) @n @r) midx midy
                k <- fullAdded z w c
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) k
                return $ V.unsafeToVector (zs <> [k])


    strictSub (UInt x) (UInt y) = UInt (circuitF $ V.unsafeToVector <$> solve)
        where
            t :: a
            t = (one + one) ^ registerSize @a @n @r - one

            solve :: MonadCircuit i a m => m [i]
            solve = do
                is <- runCircuit x
                js <- runCircuit y
                case V.fromVector $ Z.zip is js of
                  []              -> return []
                  [(i, j)]        -> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadCircuit i a m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned (\v -> v i - v j)
                _ <- expansion (highRegisterSize @a @n @r) z
                return [z]

            solveN :: MonadCircuit i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @a @n @r) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                k' <- newAssigned (\v -> v i' - v j')
                s' <- newAssigned (\v -> v k' + v b - one)
                _ <- expansion (highRegisterSize @a @n @r) s'
                return (k : zs <> [s'])


            fullSub :: MonadCircuit i a m => i -> i -> i -> m (i, i)
            fullSub xk yk b = do
                k <- newAssigned (\v -> v xk - v yk)
                s <- newAssigned (\v -> v k + v b + fromConstant t)
                splitExpansion (registerSize @a @n @r) 1 s

    strictMul (UInt x) (UInt y) = UInt (circuitF $ V.unsafeToVector <$> solve)
        where
            solve :: MonadCircuit i a m => m [i]
            solve = do
                is <- runCircuit x
                js <- runCircuit y
                case V.fromVector $ Z.zip is js of
                  []              -> return []
                  [(i, j)]        -> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadCircuit i a m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned $ \v -> v i * v j
                _ <- expansion (highRegisterSize @a @n @r) z
                return [z]

            solveN :: MonadCircuit i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @a @n @r
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @a @n @r) (registerSize @a @n @r) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n @r) (maxOverflow @a @n @r) s
                -- high register
                p' <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v l + v k')) c' [0 .. r -! 1]
                _ <- expansion (highRegisterSize @a @n @r) p'
                -- all addends higher should be zero
                for_ [r .. r * 2 -! 2] $ \k ->
                    for_ [k -! r + 1 .. r -! 1] $ \l ->
                        constraint (\v -> v (cs ! l) * v (ds ! (k -! l)))
                return (p : ps <> [p'])


--------------------------------------------------------------------------------

fullAdder :: (Arithmetic a, MonadCircuit i a m) => Natural -> i -> i -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadCircuit i a m => i -> i -> i -> m i
fullAdded i j c = do
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)
