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
import           Control.Monad.State                                       (StateT (..), runState)
import           Data.Foldable                                             (foldr, foldrM, for_)
import           Data.Functor                                              ((<$>))
import           Data.Kind                                                 (Type)
import           Data.List                                                 (unfoldr, zip)
import           Data.Map                                                  (fromList, (!))
import           Data.Traversable                                          (Traversable, for, traverse)
import           Data.Tuple                                                (swap)
import qualified Data.Zip                                                  as Z
import           GHC.Generics                                              (Generic, Par1 (..))
import           GHC.Natural                                               (naturalFromInteger)
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
import           ZkFold.Symbolic.Class                                     hiding (embed)
import           ZkFold.Symbolic.Compiler                                  hiding (forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedV, expansion, splitExpansion, horner)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.FieldElement                         (FieldElementData (..))
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Interpreter                               (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit                              (newAssigned, MonadCircuit (constraint, newRanged))
import           Data.Monoid                                         (mempty)


-- TODO (Issue #18): hide this constructor
newtype UInt (n :: Natural) (r :: RegisterSize) (backend :: (Type -> Type) -> Type) = UInt (backend (Vector (NumberOfRegisters (BaseField backend) n r)))

deriving instance Generic (UInt n r backend)
deriving instance (NFData (backend (Vector (NumberOfRegisters (BaseField backend) n r)))) => NFData (UInt n r backend)
deriving instance (Haskell.Eq (backend (Vector (NumberOfRegisters (BaseField backend) n r)))) => Haskell.Eq (UInt n r backend)
deriving instance (Haskell.Show (BaseField backend), Haskell.Show (backend (Vector (NumberOfRegisters (BaseField backend) n r)))) => Haskell.Show (UInt n r backend)

instance Arithmetic a => FieldElementData (Interpreter a) (UInt n r (Interpreter a)) where
    type TypeSize (Interpreter a) (UInt n r (Interpreter a)) = NumberOfRegisters a n r

    toFieldElements (UInt c) = c

    fromFieldElements = UInt

instance (KnownNat n, Finite (Zp p), KnownRegisterSize r) => FromConstant Natural (UInt n r (Interpreter (Zp p))) where
    fromConstant c =  case regSize @r of
        Auto ->
            let (lo, hi, _) = cast @(Zp p) @n @r . (`Haskell.mod` (2 ^ getNatural @n)) $ c
            in UInt $ Interpreter $ V.unsafeToVector $ (fromConstant <$> lo) <> [fromConstant hi]

        Fixed rs -> 
            let (lo, hi, _) = cast @(Zp p) @n @r . (`Haskell.mod` (2 ^ rs)) $ c
            in UInt $ Interpreter $ V.unsafeToVector $ (fromConstant <$> lo) <> [fromConstant hi]
            
instance (KnownNat n, Finite (Zp p), KnownRegisterSize r) => FromConstant Integer (UInt n r (Interpreter (Zp p))) where
    fromConstant = case regSize @r of
        Auto -> fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))
        Fixed rs -> fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ rs))

instance
    ( FromConstant Natural a
    , Arithmetic a
    , KnownNat n
    , KnownRegisterSize r
    ) => FromConstant Natural (UInt n r (ArithmeticCircuit a)) where
    fromConstant c = case regSize @r of
        Auto ->
            let (lo, hi, _) = cast @a @n @r . (`Haskell.mod` (2 ^ getNatural @n)) $ c
            in UInt $ embedV $ Vector $ fromConstant <$> (lo <> [hi])
        Fixed rs -> 
            let cs = (c `Haskell.mod` base) : replicate (numberOfRegisters @a @n @r -! 1) zero
                base = (2 :: Natural) ^ rs
                v = Vector $ fromConstant <$> cs ::  Vector (NumberOfRegisters a n r) a
                f = for v $ \x -> newAssigned $ fromConstant x
                (os, r) = runState f (mempty :: Circuit a) 
            in UInt $ ArithmeticCircuit { acCircuit = r {acRange = fromList [(1, fromConstant base - one)]}, acOutput = os }

instance
    ( FromConstant Natural a
    , Arithmetic a
    , KnownNat n
    , KnownRegisterSize r
    ) => FromConstant Integer (UInt n r (ArithmeticCircuit a)) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural (UInt n r b), KnownNat n, MultiplicativeSemigroup (UInt n r b)) => Scale Natural (UInt n r b)

instance (FromConstant Integer (UInt n r b), KnownNat n, MultiplicativeSemigroup (UInt n r b)) => Scale Integer (UInt n r b)

instance MultiplicativeMonoid (UInt n r b) => Exponent (UInt n r b) Natural where
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
    :: forall n b r
    .  EuclideanDomain (UInt n r b)
    => KnownNat n
    => AdditiveGroup (UInt n r b)
    => Eq (Bool b) (UInt n r b)
    => Conditional (Bool b) (UInt n r b, UInt n r b, UInt n r b)
    => UInt n r b -> UInt n r b -> (UInt n r b, UInt n r b, UInt n r b)
eea a b = eea' 1 a b one zero zero one
    where
        iterations :: Natural
        iterations = value @n * 2 + 1

        eea' :: Natural -> UInt n r b -> UInt n r b -> UInt n r b -> UInt n r b -> UInt n r b -> UInt n r b -> (UInt n r b, UInt n r b, UInt n r b)
        eea' iteration oldR r oldS s oldT t
          | iteration Haskell.== iterations = (oldS, oldT, oldR)
          | otherwise = bool @(Bool b) rec (if Haskell.even iteration then b - oldS else oldS, if Haskell.odd iteration then a - oldT else oldT, oldR) (r == zero)
            where
                quotient = oldR `div` r

                rec = eea' (iteration + 1) r (oldR - quotient * r) s (quotient * s + oldS) t (quotient * t + oldT)

--------------------------------------------------------------------------------

instance (Finite (Zp p), KnownNat n, KnownNat m, n <= m, KnownRegisterSize r) => Extend (UInt n r (Interpreter (Zp p))) (UInt m r (Interpreter (Zp p))) where
    extend = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownNat m, m <= n, KnownRegisterSize r) => Shrink (UInt n r (Interpreter (Zp p))) (UInt m r (Interpreter (Zp p))) where
    shrink = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Eq (Bool (Interpreter (Zp p))) (UInt n r (Interpreter (Zp p))) where
    x == y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.== toConstant y
    x /= y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell./= toConstant y

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Ord (Bool (Interpreter (Zp p))) (UInt n r (Interpreter (Zp p))) where
    x <= y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.<= toConstant y
    x < y  = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.< toConstant y
    x >= y = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.>= toConstant y
    x > y  = Bool . Interpreter . Par1 . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.> toConstant y
    max x y = fromConstant $ Haskell.max (toConstant @_ @Natural x) (toConstant y)
    min x y = fromConstant $ Haskell.min (toConstant @_ @Natural x) (toConstant y)

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter (Zp p))) Natural where
    toConstant (UInt (Interpreter xs)) = 
        foldr (\p y -> fromZp p + base * y) 0 xs
        where base = 2 ^ registerSize @(Zp p) @n @r

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter (Zp p))) Integer where
    toConstant = Haskell.fromIntegral @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => AdditiveSemigroup (UInt n r (Interpreter (Zp p))) where
    x + y = fromConstant $ toConstant x + toConstant @_ @Natural y

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => AdditiveMonoid (UInt n r (Interpreter (Zp p))) where
    zero = fromConstant (0 :: Natural)

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => AdditiveGroup (UInt n r (Interpreter (Zp p))) where
    x - y = fromConstant $ toConstant x + 2 ^ getNatural @n -! toConstant y
    negate x = fromConstant $ 2 ^ getNatural @n -! toConstant x

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => MultiplicativeSemigroup (UInt n r (Interpreter (Zp p))) where
    x * y = fromConstant $ toConstant x * toConstant @_ @Natural y

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => MultiplicativeMonoid (UInt n r (Interpreter (Zp p))) where
    one = fromConstant (1 :: Natural)

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Semiring (UInt n r (Interpreter (Zp p)))

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Ring (UInt n r (Interpreter (Zp p)))

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Arbitrary (UInt n r (Interpreter (Zp p))) where
    arbitrary = case regSize @r of
        Auto -> do
            lo <- replicateA (numberOfRegisters @(Zp p) @n @r -! 1) (toss $ registerSize @(Zp p) @n @r)
            hi <- toss (highRegisterSize @(Zp p) @n @r)
            return $ UInt $ Interpreter $ V.unsafeToVector (lo <> [hi])
        Fixed rs -> do
            lst <- toss rs
            let int = replicate (numberOfRegisters @(Zp p) @n @r -! 1) zero
            return $ UInt $ Interpreter $ V.unsafeToVector ([lst] <> int)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Iso (ByteString n (Interpreter (Zp p))) (UInt n r (Interpreter (Zp p))) where
    from = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => Iso (UInt n r (Interpreter (Zp p))) (ByteString n (Interpreter (Zp p))) where
    from = fromConstant @Natural . toConstant

--------------------------------------------------------------------------------

instance Arithmetic a => SymbolicData a (UInt n r (ArithmeticCircuit a)) where
    type Support a (UInt n r (ArithmeticCircuit a)) = ()
    type TypeSize a (UInt n r (ArithmeticCircuit a)) = NumberOfRegisters a n r

    pieces (UInt c) _ = c
    restore = UInt . ($ ())


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat k
    , KnownRegisterSize r
    , n <= k
    , from ~ NumberOfRegisters a n r
    , to ~ NumberOfRegisters a k r
    ) => Extend (UInt n r (ArithmeticCircuit a)) (UInt k r (ArithmeticCircuit a)) where
    extend (UInt ac) = UInt (circuitF solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m (Vector to i)
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @a @n @r) (registerSize @a @n @r)
                zeros <- replicateA (value @k -! (value @n)) (newAssigned (Haskell.const zero))
                extended <- fromBits (highRegisterSize @a @k @r) (registerSize @a @k @r) (zeros <> bsBits)
                return $ V.unsafeToVector $ Haskell.reverse extended

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat k
    , KnownRegisterSize r
    , k <= n
    , from ~ NumberOfRegisters a n r
    , to ~ NumberOfRegisters a k r
    ) => Shrink (UInt n r (ArithmeticCircuit a)) (UInt k r (ArithmeticCircuit a)) where
    shrink (UInt ac) = UInt (circuitF solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m (Vector to i)
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @a @n @r) (registerSize @a @n @r)
                shrinked <- fromBits (highRegisterSize @a @k @r) (registerSize @a @k @r) (drop (value @n -! (value @k)) bsBits)
                return $ V.unsafeToVector $ Haskell.reverse shrinked

instance
    ( KnownNat n
    , KnownNat r
    , KnownNat (r - 1)
    , KnownNat (r + r)
    , KnownRegisterSize rs
    , r ~ NumberOfRegisters (BaseField b) n rs
    , NFData (b (Vector r))
    , Ord (Bool b) (UInt n rs b)
    , AdditiveGroup (UInt n rs b)
    , Semiring (UInt n rs b)
    , MultiplicativeMonoid (UInt n rs b)
    , FromConstant Natural (UInt n rs b)
    , BitState ByteString n b
    , Iso (ByteString n b) (UInt n rs b)
    , Eq (Bool b) (UInt n rs b)
    , Conditional (Bool b) (UInt n rs b)
    , Conditional (Bool b) (UInt n rs b, UInt n rs b)
    , 1 + (r - 1) ~ r
    , 1 <= r
    ) => EuclideanDomain (UInt n rs b) where
    divMod numerator d = bool @(Bool b) (q, r) (zero, zero) (d == zero)
        where
            (q, r) = Haskell.foldl longDivisionStep (zero, zero) [value @n -! 1, value @n -! 2 .. 0]

            numeratorBits :: ByteString n b
            numeratorBits = from numerator

            addBit :: UInt n rs b -> Natural -> UInt n rs b
            addBit ui bs = ui + bool @(Bool b) zero one (isSet numeratorBits bs)

            longDivisionStep
                :: (UInt n rs b, UInt n rs b)
                -> Natural
                -> (UInt n rs b, UInt n rs b)
            longDivisionStep (q', r') i =
                let rs = force $ addBit (r' + r') (value @n -! i -! 1)
                 in bool @(Bool b) (q', rs) (q' + fromConstant ((2 :: Natural) ^ i), rs - d) (rs >= d)

instance (Arithmetic a, KnownNat n, KnownRegisterSize r, KnownNat (NumberOfRegisters a n r)) => Ord (Bool (ArithmeticCircuit a)) (UInt n r (ArithmeticCircuit a)) where
    x <= y = y >= x

    x <  y = y > x

    u1 >= u2 =
        let ByteString rs1 = from u1 :: ByteString n (ArithmeticCircuit a)
            ByteString rs2 = from u2 :: ByteString n (ArithmeticCircuit a)
         in circuitGE rs1 rs2

    u1 > u2 =
        let ByteString rs1 = from u1 :: ByteString n (ArithmeticCircuit a)
            ByteString rs2 = from u2 :: ByteString n (ArithmeticCircuit a)
         in circuitGT rs1 rs2

    max x y = bool @(Bool (ArithmeticCircuit a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit a)) x y $ x > y


instance (Arithmetic a, KnownNat n, KnownRegisterSize r) => AdditiveSemigroup (UInt n r (ArithmeticCircuit a)) where
    UInt x + UInt y = case regSize @r of
        Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    j <- newAssigned (Haskell.const zero)
                    z <- Haskell.head . V.fromVector <$> runCircuit x
                    w <- Haskell.head . V.fromVector <$> runCircuit y
                    let base = (2 :: Natural) ^ (rs :: Natural)
                    (k, _) <- newRanged (fromConstant base - one) (\v -> v z + v w) >>= splitExpansion rs 1
                    return (k: replicate (numberOfRegisters @a @n @r -! 1) j)

        Auto -> UInt (circuitF $ V.unsafeToVector <$> solve)
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
                        Haskell.zipWith (fullAdder $ registerSize @a @n @r) midx midy
                    k <- fullAdded z w c
                    (ks, _) <- splitExpansion (highRegisterSize @a @n @r) 1 k
                    return (zs ++ [ks])

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat (NumberOfRegisters a n r)
    , KnownRegisterSize r
    ) => AdditiveMonoid (UInt n r (ArithmeticCircuit a)) where
    zero = UInt zero

instance
    ( Arithmetic a
    , KnownNat n
    , KnownRegisterSize r
    , KnownNat (NumberOfRegisters a n r)
    ) => AdditiveGroup (UInt n r (ArithmeticCircuit a)) where

        UInt x - UInt y =  case regSize @r of
            Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
                where
                    solve :: MonadBlueprint i a m => m [i]
                    solve = do
                        j <- newAssigned (Haskell.const zero)
                        z <- Haskell.head . V.fromVector <$> runCircuit x
                        w <- Haskell.head . V.fromVector <$> runCircuit y
                        let base = (2 :: Natural) ^ (rs :: Natural)
                        (k, _) <- newRanged (fromConstant base - one) (\v -> v z - v w + fromConstant base) >>= splitExpansion rs 1
                        return (k: replicate (numberOfRegisters @a @n @r -! 1) j)

            Auto -> UInt $ circuitF (V.unsafeToVector <$> solve)
                where
                    t :: a
                    t = (one + one) ^ registerSize @a @n @r - one

                    solve :: MonadBlueprint i a m => m [i]
                    solve = do
                        is <- runCircuit x
                        js <- runCircuit y
                        case V.fromVector $ Z.zip is js of
                            []              -> return []
                            [(i, j)]        -> solve1 i j
                            ((i, j) : rest) ->  let (z, w) = Haskell.last rest
                                                    (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                                in solveN (i, j) (ris, rjs) (z, w)

                    solve1 :: MonadBlueprint i a m => i -> i -> m [i]
                    solve1 i j = do
                        z0 <- newAssigned (\v -> v i - v j + fromConstant (2 ^ registerSize @a @n @r :: Natural))
                        (z, _) <- splitExpansion (highRegisterSize @a @n @r) 1 z0
                        return [z]

                    solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
                    solveN (i, j) (is, js) (i', j') = do
                        s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                        (k, b0) <- splitExpansion (registerSize @a @n @r) 1 s
                        (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                        d <- newAssigned (\v -> v i' - v j')
                        s'0 <- newAssigned (\v -> v d + v b + fromConstant t)
                        (s', _) <- splitExpansion (highRegisterSize @a @n @r) 1 s'0
                        return (k : zs <> [s'])

                    fullSub :: MonadBlueprint i a m => i -> i -> i -> m (i, i)
                    fullSub xk yk b = do
                        d <- newAssigned (\v -> v xk - v yk)
                        s <- newAssigned (\v -> v d + v b + fromConstant t)
                        splitExpansion (registerSize @a @n @r) 1 s

        negate (UInt x) = case regSize @r of
            Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
                where
                    solve :: MonadBlueprint i a m => m [i]
                    solve = do
                        j <- newAssigned (Haskell.const zero)
                        z <- Haskell.head . V.fromVector <$> runCircuit x
                        let base = (2 :: Natural) ^ (rs :: Natural)
                        (k, _) <- newRanged (fromConstant base - one) (\v -> fromConstant base - v z) >>= splitExpansion rs 1
                        return (k: replicate (numberOfRegisters @a @n @r -! 1) j)

            Auto ->
                let y = 2 ^ registerSize @a @n @r
                    ys = replicate (numberOfRegisters @a @n @r -! 2) (2 ^ registerSize @a @n @r -! 1)
                    y' = 2 ^ highRegisterSize @a @n @r -! 1
                    ns
                        | numberOfRegisters @a @n @r Haskell.== 1 = V.unsafeToVector [y' + 1]
                        | otherwise = V.unsafeToVector $ (y : ys) <> [y']
                in UInt (negateN ns x)

negateN :: (Arithmetic a, Z.Zip f, Traversable f) => f Natural -> ArithmeticCircuit a f -> ArithmeticCircuit a f
negateN ns r = circuitF $ do
    is <- runCircuit r
    for (Z.zip is ns) $ \(i, n) -> newAssigned (\v -> fromConstant n - v i)

            -- Auto -> UInt (circuitF $ V.unsafeToVector <$> solve)
            --     where
            --     solve :: MonadBlueprint i a m => m [i]
            --     solve = do
            --         j <- newAssigned (Haskell.const zero)

            --         let lo = fromConstant $ (2 :: Natural) ^ registerSize @a @n @r
            --             mid = replicate (numberOfRegisters @a @n @r -! 2) (fromConstant $ (2 :: Natural) ^ registerSize @a @n @r -! 1)
            --             hi = fromConstant $ (2 :: Natural) ^ highRegisterSize @a @n @r -! 1
            --             y = embedV $ V.unsafeToVector ([lo] <> mid <> [hi])

            --         xs <- V.fromVector <$> runCircuit x
            --         ys <- V.fromVector <$> runCircuit y
            --         let midx = Haskell.init xs
            --             z    = Haskell.last xs
            --             midy = Haskell.init ys
            --             w    = Haskell.last ys
            --         (zs, c) <- flip runStateT j $ traverse StateT $
            --             Z.zipWith (fullNegater $ registerSize @a @n @r) midy midx
            --         k <- fullNegated w z c
            --         (ks, _) <- splitExpansion (highRegisterSize @a @n @r) 1 k
            --         return (zs ++ [ks])


instance (Arithmetic a, KnownNat n, KnownRegisterSize rs, r ~ NumberOfRegisters a n rs) => MultiplicativeSemigroup (UInt n rs (ArithmeticCircuit a)) where
    UInt x * UInt y = case regSize @rs of
        Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    j <- newAssigned (Haskell.const zero)
                    z <- Haskell.head . V.fromVector <$> runCircuit x
                    w <- Haskell.head . V.fromVector <$> runCircuit y
                    let base = (2 :: Natural) ^ (rs :: Natural)
                    (k, _) <- newRanged (fromConstant base - one) (\v -> v z * v w ) >>= splitExpansion rs (maxOverflow @a @n @rs)
                    return (k: replicate (numberOfRegisters @a @n @rs -! 1) j)

        Auto -> UInt (circuitF $ V.unsafeToVector <$> solve)
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    is <- runCircuit x
                    js <- runCircuit y
                    case V.fromVector $ Z.zip is js of
                        []              -> return []
                        [(i, j)]        -> solve1 i j
                        ((i, j) : rest) ->  let (z, w) = Haskell.last rest
                                                (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                            in solveN (i, j) (ris, rjs) (z, w)

                solve1 :: MonadBlueprint i a m => i -> i -> m [i]
                solve1 i j = do
                    (z, _) <- newAssigned (\v -> v i * v j) >>= splitExpansion (highRegisterSize @a @n @rs) (maxOverflow @a @n @rs)
                    return [z]

                solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
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

    one = UInt $ hliftA2 (\(Par1 h) t -> h V..: t) (one :: ArithmeticCircuit a Par1) (zero :: ArithmeticCircuit a (Vector (NumberOfRegisters a n r - 1)))


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
         instance (Arithmetic a, KnownNat r, r ~ NumberOfRegisters a n rs, 1 <= r) =>
         Eq (Bool (ArithmeticCircuit a)) (UInt n rs (ArithmeticCircuit a))

instance (Arithmetic a, KnownNat n, KnownRegisterSize r) => Arbitrary (UInt n r (ArithmeticCircuit a)) where
    arbitrary = case regSize @r of
        Auto -> do
            lows <- replicateA (numberOfRegisters @a @n @r -! 1) (toss $ registerSize @a @n @r)
            hi <- toss (highRegisterSize @a @n @r)
            return $ UInt $ embedV (V.unsafeToVector $ lows <> [hi])
        Fixed rs -> do
            c  :: Integer <- toss $ registerSize @a @n @r
            let cs = c : replicate (numberOfRegisters @a @n @r -! 1) zero
                base = (2 :: Natural) ^ rs
                v = Vector $ fromConstant <$> cs ::  Vector (NumberOfRegisters a n r) a
                f = for v $ \x -> newAssigned $ fromConstant x
                (os, r) = runState f (mempty :: Circuit a) 
            return $ UInt $ ArithmeticCircuit { acCircuit = r {acRange = fromList [(1, fromConstant base - one)]}, acOutput = os }
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Arithmetic a, KnownNat n, KnownRegisterSize r) => Iso (ByteString n (ArithmeticCircuit a)) (UInt n r (ArithmeticCircuit a)) where
    from (ByteString bits) = UInt (circuitF $ V.unsafeToVector <$> solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- V.fromVector <$> runCircuit bits
                Haskell.reverse <$> fromBits (highRegisterSize @a @n @r) (registerSize @a @n @r) bsBits

instance (Arithmetic a, KnownNat n, KnownRegisterSize r) => Iso (UInt n r (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where
    from (UInt ac) = ByteString $ circuitF $ Vector <$> solve
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                regs <- V.fromVector <$> runCircuit ac
                toBits (Haskell.reverse regs) (highRegisterSize @a @n @r) (registerSize @a @n @r)


--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => StrictConv Natural (UInt n r (Interpreter (Zp p))) where
    strictConv n = case regSize @r of
        Auto -> case cast @(Zp p) @n @r n of
            (lo, hi, []) -> UInt $ Interpreter $ V.unsafeToVector $ (toZp . Haskell.fromIntegral <$> lo) <> [toZp . Haskell.fromIntegral $ hi]
            _            -> error "strictConv: overflow"
        Fixed rs -> 
            let ns = replicate (numberOfRegisters @(Zp p) @n @r -! 1) 0
            in case div n (2 ^ rs) of
                0 -> UInt $ Interpreter $ V.unsafeToVector $ (toZp . Haskell.fromIntegral <$> [n]) <> (toZp <$> ns)
                _ -> error "strictConv: overflow"

instance (FromConstant Natural a, Arithmetic a, KnownNat n, KnownRegisterSize rs, r ~ NumberOfRegisters a n rs) => StrictConv Natural (UInt n rs (ArithmeticCircuit a)) where
    strictConv n = case regSize @rs of
        Auto -> case cast @a @n @rs n of
            (lo, hi, []) -> UInt $ embedV $ V.unsafeToVector $ fromConstant <$> (lo <> [hi])
            _            -> error "strictConv: overflow"
        Fixed rs -> 
            let ns = replicate (numberOfRegisters @a @n @rs -! 1) 0
            in case div n (2 ^ rs) of
                0 -> UInt $ embedV $ V.unsafeToVector $ fromConstant <$> n: ns
                _ -> error "strictConv: overflow"

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => StrictConv (Zp p) (UInt n r (Interpreter (Zp p))) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Finite (Zp p), Prime p, KnownNat n, KnownRegisterSize r) => StrictConv (Zp p) (UInt n r (ArithmeticCircuit (Zp p))) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Arithmetic a, KnownNat n, KnownRegisterSize r, NumberOfBits a <= n) => StrictConv (ArithmeticCircuit a Par1) (UInt n r (ArithmeticCircuit a)) where
    strictConv a = UInt (circuitF $ V.unsafeToVector <$> solve)
        where
            requiredBits :: Natural
            requiredBits = (numberOfRegisters @a @n @r -! 1) * (registerSize @a @n @r) + (highRegisterSize @a @n @r)

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- unPar1 <$> runCircuit a
                bits <- Haskell.reverse <$> expansion requiredBits i -- why count RequiredBits if we can use getNatural @n?
                fromBits (highRegisterSize @a @n @r) (registerSize @a @n @r) bits


class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Finite (Zp p), KnownNat n, KnownRegisterSize r) => StrictNum (UInt n r (Interpreter (Zp p))) where
    strictAdd x y = strictConv $ toConstant x + toConstant @_ @Natural y
    strictSub x y = strictConv $ toConstant x -! toConstant y
    strictMul x y = strictConv $ toConstant x * toConstant @_ @Natural y

instance (Arithmetic a, KnownNat n, KnownRegisterSize r) => StrictNum (UInt n r (ArithmeticCircuit a)) where
    strictAdd (UInt x) (UInt y) = case regSize @r of
        Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    j <- newAssigned (Haskell.const zero)
                    z <- Haskell.head . V.fromVector <$> runCircuit x
                    w <- Haskell.head . V.fromVector <$> runCircuit y
                    let base = (2 :: Natural) ^ (rs :: Natural)
                    k <- newRanged (fromConstant base - one) (\v -> v z + v w) >>= expansion rs >>= horner
                    return (k: replicate (numberOfRegisters @a @n @r -! 1) j)

        Auto -> UInt (circuitF $ V.unsafeToVector <$> solve)
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
                        Haskell.zipWith (fullAdder $ registerSize @a @n @r) midx midy
                    k <- fullAdded z w c
                    _ <- expansion (highRegisterSize @a @n @r) k
                    return (zs <> [k])


    strictSub (UInt x) (UInt y) = case regSize @r of
        Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    j <- newAssigned (Haskell.const zero)
                    z <- Haskell.head . V.fromVector <$> runCircuit x
                    w <- Haskell.head . V.fromVector <$> runCircuit y
                    let base = (2 :: Natural) ^ (rs :: Natural)
                    k <- newRanged (fromConstant base - one) (\v -> v z - v w + fromConstant base) >>= expansion rs >>= horner
                    return (k: replicate (numberOfRegisters @a @n @r -! 1) j)

        Auto -> UInt (circuitF $ V.unsafeToVector <$> solve)
            where
                t :: a
                t = (one + one) ^ registerSize @a @n @r - one

                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    is <- runCircuit x
                    js <- runCircuit y
                    case V.fromVector $ Z.zip is js of
                        []              -> return []
                        [(i, j)]        -> solve1 i j
                        ((i, j) : rest) ->  let (z, w) = Haskell.last rest
                                                (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                            in solveN (i, j) (ris, rjs) (z, w)

                solve1 :: MonadBlueprint i a m => i -> i -> m [i]
                solve1 i j = do
                    z <- newAssigned (\v -> v i - v j)
                    _ <- expansion (highRegisterSize @a @n @r) z
                    return [z]

                solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
                solveN (i, j) (is, js) (i', j') = do
                    s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                    (k, b0) <- splitExpansion (registerSize @a @n @r) 1 s
                    (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                    k' <- newAssigned (\v -> v i' - v j')
                    s' <- newAssigned (\v -> v k' + v b - one)
                    _ <- expansion (highRegisterSize @a @n @r) s'
                    return (k : zs <> [s'])


                fullSub :: MonadBlueprint i a m => i -> i -> i -> m (i, i)
                fullSub xk yk b = do
                    k <- newAssigned (\v -> v xk - v yk)
                    s <- newAssigned (\v -> v k + v b + fromConstant t)
                    splitExpansion (registerSize @a @n @r) 1 s

    strictMul (UInt x) (UInt y) =  case regSize @r of
        Fixed rs -> UInt $ circuitF $ V.unsafeToVector <$> solve
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    j <- newAssigned (Haskell.const zero)
                    z <- Haskell.head . V.fromVector <$> runCircuit x
                    w <- Haskell.head . V.fromVector <$> runCircuit y
                    let base = (2 :: Natural) ^ (rs :: Natural)
                    k <- newRanged (fromConstant base - one) (\v -> v z * v w ) >>= expansion rs >>= horner
                    return (k: replicate (numberOfRegisters @a @n @r -! 1) j)

        Auto -> UInt (circuitF $ V.unsafeToVector <$> solve)
            where
                solve :: MonadBlueprint i a m => m [i]
                solve = do
                    is <- runCircuit x
                    js <- runCircuit y
                    case V.fromVector $ Z.zip is js of
                        []              -> return []
                        [(i, j)]        -> solve1 i j
                        ((i, j) : rest) ->  let (z, w) = Haskell.last rest
                                                (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                            in solveN (i, j) (ris, rjs) (z, w)

                solve1 :: MonadBlueprint i a m => i -> i -> m [i]
                solve1 i j = do
                    z <- newAssigned $ \v -> v i * v j
                    _ <- expansion (highRegisterSize @a @n @r) z
                    return [z]

                solveN :: MonadBlueprint i a m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
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

fullAdder :: MonadBlueprint i a m => Natural -> i -> i -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadBlueprint i a m => i -> i -> i -> m i
fullAdded i j c = do
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)

fullNegater :: MonadBlueprint i a m => Natural -> i -> i -> i -> m (i, i)
fullNegater r xk yk c = fullNegated xk yk c >>= splitExpansion r 1

fullNegated :: MonadBlueprint i a m => i -> i -> i -> m i
fullNegated i j c = do
    k <- newAssigned (\v -> v i - v j)
    newAssigned (\v -> v k + v c)
