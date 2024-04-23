{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.UInt (
    StrictConv(..),
    StrictNum(..),
    UInt(..),
    toConstant
) where

import           Control.Applicative                                       ((<*>))
import           Control.Monad.State                                       (StateT (..))
import           Data.Foldable                                             (foldr, foldrM, for_)
import           Data.Functor                                              ((<$>))
import           Data.List                                                 (map, unfoldr, zip, zipWith)
import           Data.Map                                                  (fromList, (!))
import           Data.Traversable                                          (for, traverse)
import           Data.Tuple                                                (swap)
import qualified Data.Vector                                               as V
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (KnownNat, Natural)
import           Prelude                                                   (Integer, error, flip, otherwise, return,
                                                                            ($), (.), (>>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, fromZp)
import           ZkFold.Prelude                                            (length, splitAt)
import           ZkFold.Symbolic.Compiler                                  hiding (forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, splitExpansion)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Combinators

-- TODO (Issue #18): hide this constructor
data UInt (n :: Natural) a = UInt !(V.Vector a) !a
    deriving (Haskell.Show, Haskell.Eq)

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Natural (UInt n a) where
    fromConstant = Haskell.fst . cast @a @n . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Integer (UInt n a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n a)) => Scale Natural (UInt n a)

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n a)) => Scale Integer (UInt n a)

instance MultiplicativeMonoid (UInt n a) => Exponent (UInt n a) Natural where
    (^) = natPow

cast :: forall a n . (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => Natural -> (UInt n a, [a])
cast n =
    let base = 2 ^ registerSize @a @n
        registers = map fromConstant $ flip unfoldr n $ \case
            0 -> Haskell.Nothing
            x -> Haskell.Just (swap $ x `Haskell.divMod` base)
        r = numberOfRegisters @a @n -! 1
     in case greedySplitAt r registers of
        (lo, hi:rest) -> (UInt (V.fromList lo) hi, rest)
        (lo, [])      -> (UInt (V.fromList lo Haskell.<> V.replicate (Haskell.fromIntegral (r -! length lo)) zero) zero, [])
    where
        greedySplitAt 0 xs = ([], xs)
        greedySplitAt _ [] = ([], [])
        greedySplitAt m (x : xs) =
            let (ys, zs) = greedySplitAt (m -! 1) xs
             in (x : ys, zs)

--------------------------------------------------------------------------------

instance (KnownNat p, KnownNat n) => ToConstant (UInt n (Zp p)) Natural where
    toConstant (UInt xs x) = foldr (\p y -> fromZp p + base * y) 0 (xs `V.snoc` x)
        where base = 2 ^ registerSize @(Zp p) @n

instance (KnownNat p, KnownNat n) => AdditiveSemigroup (UInt n (Zp p)) where
    x + y = fromConstant $ toConstant x + toConstant @_ @Natural y

instance (KnownNat p, KnownNat n) => AdditiveMonoid (UInt n (Zp p)) where
    zero = fromConstant (0 :: Natural)

instance (KnownNat p, KnownNat n) => AdditiveGroup (UInt n (Zp p)) where
    x - y = fromConstant $ toConstant x + 2 ^ getNatural @n -! toConstant y
    negate x = fromConstant $ 2 ^ getNatural @n -! toConstant x

instance (KnownNat p, KnownNat n) => MultiplicativeSemigroup (UInt n (Zp p)) where
    x * y = fromConstant $ toConstant x * toConstant @_ @Natural y

instance (KnownNat p, KnownNat n) => MultiplicativeMonoid (UInt n (Zp p)) where
    one = fromConstant (1 :: Natural)

instance (KnownNat p, KnownNat n) => Semiring (UInt n (Zp p))

instance (KnownNat p, KnownNat n) => Ring (UInt n (Zp p))

instance (KnownNat p, KnownNat n) => Arbitrary (UInt n (Zp p)) where
    arbitrary = UInt
        <$> V.replicateM (Haskell.fromIntegral (numberOfRegisters @(Zp p) @n -! 1)) (toss $ registerSize @(Zp p) @n)
        <*> toss (highRegisterSize @(Zp p) @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n) => SymbolicData a (UInt n (ArithmeticCircuit a)) where
    pieces (UInt as a) = V.toList (as `V.snoc` a)

    restore as = case splitAt (numberOfRegisters @a @n -! 1) as of
        (lo, [hi]) -> UInt (V.fromList lo) hi
        (_, _)     -> error "UInt: invalid number of values"

    typeSize = numberOfRegisters @a @n

instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt vx x0 + UInt vy y0 = case (V.uncons vx, x0, V.uncons vy, y0) of

      (Haskell.Nothing, x, Haskell.Nothing, y) -> UInt V.empty $ circuit $ do
        (z, _) <- runCircuit (x + y) >>= splitExpansion (highRegisterSize @a @n) 1
        return z

      (Haskell.Just (x,xs), z, Haskell.Just (y,ys), w) ->
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                (i, j) <- runCircuit (x + y) >>= splitExpansion (registerSize @a @n) 1
                (zs, c) <- flip runStateT j $ traverse StateT $
                    zipWith (fullAdder $ registerSize @a @n) (V.toList xs) (V.toList ys)
                (k, _) <- fullAdder (highRegisterSize @a @n) z w c
                return (k : i : zs)

         in case circuits solve of
            (hi : lo) -> UInt (V.fromList lo) hi
            []        -> error "UInt: unreachable"

      _ -> error "UInt: unreachable"

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (UInt n (ArithmeticCircuit a)) where
    zero = UInt (V.replicate (Haskell.fromIntegral (numberOfRegisters @a @n -! 1)) zero) zero

instance (Arithmetic a, KnownNat n) => AdditiveGroup (UInt n (ArithmeticCircuit a)) where
    UInt vx x0 - UInt vy y0 = case (V.uncons vx, x0, V.uncons vy, y0) of

      (Haskell.Nothing, x, Haskell.Nothing, y) -> UInt V.empty $ circuit $ do
        i <- runCircuit x
        j <- runCircuit y
        z0 <- newAssigned (\v -> v i - v j + fromConstant (2 ^ registerSize @a @n :: Natural))
        (z, _) <- splitExpansion (highRegisterSize @a @n) 1 z0
        return z

      (Haskell.Just (x,xs), z, Haskell.Just (y,ys), w) ->
        let t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (zipWith fullSub (V.toList xs) (V.toList ys))
                d <- runCircuit (z - w)
                s'0 <- newAssigned (\v -> v d + v b + fromConstant t)
                (s', _) <- splitExpansion (highRegisterSize @a @n) 1 s'0
                return (s' : k : zs)

            fullSub :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullSub xk yk b = do
                d <- runCircuit (xk - yk)
                s <- newAssigned (\v -> v d + v b + fromConstant t)
                splitExpansion (registerSize @a @n) 1 s

         in case circuits solve of
            (hi : lo) -> UInt (V.fromList lo) hi
            []        -> error "UInt: unreachable"

      _ -> error "UInt: unreachable"

    negate (UInt vs x0) = case (V.uncons vs, x0) of
      (Haskell.Nothing, x) -> UInt V.empty (negateN (2 ^ highRegisterSize @a @n) x)
      (Haskell.Just (x,xs), x') ->
        let y = negateN (2 ^ registerSize @a @n) x
            ys = V.map (negateN $ 2 ^ registerSize @a @n -! 1) xs
            y' = negateN (2 ^ highRegisterSize @a @n -! 1) x'
         in UInt (y `V.cons` ys) y'

negateN :: Arithmetic a => Natural -> ArithmeticCircuit a -> ArithmeticCircuit a
negateN n r = circuit $ do
    i <- runCircuit r
    newAssigned (\v -> fromConstant n - v i)

instance (Arithmetic a, KnownNat n) => MultiplicativeSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt vx x0 * UInt vy y0 = case (V.uncons vx, x0, V.uncons vy, y0) of

      (Haskell.Nothing, x, Haskell.Nothing, y) -> UInt V.empty $ circuit $ do
        (z, _) <- runCircuit (x * y) >>= splitExpansion (highRegisterSize @a @n) (maxOverflow @a @n)
        return z

      (Haskell.Just (x,xs), z, Haskell.Just (y,ys), w) ->
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                is <- for xs runCircuit
                js <- for ys runCircuit
                i' <- runCircuit z
                j' <- runCircuit w
                let cs = fromList $ zip [0..] (i : V.toList (is `V.snoc` i'))
                    ds = fromList $ zip [0..] (j : V.toList (js `V.snoc` j'))
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
                return (p' : p : ps)

         in case circuits solve of
            (hi : lo) -> UInt (V.fromList lo) hi
            []        -> error "UInt: unreachable"

      _ -> error "UInt: unreachable"

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (UInt n (ArithmeticCircuit a)) where
    one | numberOfRegisters @a @n Haskell.== 1 = UInt V.empty one
        | otherwise = UInt (one `V.cons` V.replicate (Haskell.fromIntegral (numberOfRegisters @a @n -! 2)) zero) zero

instance (Arithmetic a, KnownNat n) => Semiring (UInt n (ArithmeticCircuit a))

instance (Arithmetic a, KnownNat n) => Ring (UInt n (ArithmeticCircuit a))

--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => StrictConv Natural (UInt n a) where
    strictConv n = case cast @a @n n of
        (x, []) -> x
        (_, _)  -> error "strictConv: overflow"

class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (KnownNat p, KnownNat n) => StrictNum (UInt n (Zp p)) where
    strictAdd x y = strictConv $ toConstant x + toConstant @_ @Natural y
    strictSub x y = strictConv $ toConstant x -! toConstant y
    strictMul x y = strictConv $ toConstant x * toConstant @_ @Natural y

instance (Arithmetic a, KnownNat n) => StrictNum (UInt n (ArithmeticCircuit a)) where
    strictAdd (UInt vx x0) (UInt vy y0) = case (V.uncons vx, x0, V.uncons vy, y0) of

      (Haskell.Nothing, x, Haskell.Nothing, y) -> UInt V.empty $ circuit $ do
        z <- runCircuit (x + y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

      (Haskell.Just (x,xs), z, Haskell.Just (y,ys), w) ->
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                (i, j) <- runCircuit (x + y) >>= splitExpansion (registerSize @a @n) 1
                (zs, c) <- flip runStateT j $ traverse StateT $
                    zipWith (fullAdder $ registerSize @a @n) (V.toList xs) (V.toList ys)
                k <- fullAdded z w c
                _ <- expansion (highRegisterSize @a @n) k
                return (k : i : zs)

         in case circuits solve of
            (hi : lo) -> UInt (V.fromList lo) hi
            []        -> error "UInt: unreachable"

      _ -> error "UInt: unreachable"

    strictSub (UInt vx x0) (UInt vy y0) = case (V.uncons vx, x0, V.uncons vy, y0) of

      (Haskell.Nothing, x, Haskell.Nothing, y) -> UInt V.empty $ circuit $ do
        z <- runCircuit (x - y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

      (Haskell.Just (x,xs), z, Haskell.Just (y,ys), w) ->
        let t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (zipWith fullSub (V.toList xs) (V.toList ys))
                k' <- runCircuit (z - w)
                s' <- newAssigned (\v -> v k' + v b - one)
                _ <- expansion (highRegisterSize @a @n) s'
                return (s' : k : zs)

            fullSub :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullSub xk yk b = do
                k <- runCircuit (xk - yk)
                s <- newAssigned (\v -> v k + v b + fromConstant t)
                splitExpansion (registerSize @a @n) 1 s

         in case circuits solve of
            (hi : lo) -> UInt (V.fromList lo) hi
            []        -> error "UInt: unreachable"

      _ -> error "UInt: unreachable"

    strictMul (UInt vx x0) (UInt vy y0) = case (V.uncons vx, x0, V.uncons vy, y0) of

      (Haskell.Nothing, x, Haskell.Nothing, y) -> UInt V.empty $ circuit $ do
        z <- runCircuit (x * y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

      (Haskell.Just (x,xs), z, Haskell.Just (y,ys), w) ->
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                is <- for xs runCircuit
                js <- for ys runCircuit
                i' <- runCircuit z
                j' <- runCircuit w
                let cs = fromList $ zip [0..] (i : V.toList (is `V.snoc` i'))
                    ds = fromList $ zip [0..] (j : V.toList (js `V.snoc` j'))
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
                return (p' : p : ps)

         in case circuits solve of
            (hi : lo) -> UInt (V.fromList lo) hi
            []        -> error "UInt: unreachable"

      _ -> error "UInt: unreachable"

--------------------------------------------------------------------------------

fullAdder :: MonadBlueprint i a m => Natural -> ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m i
fullAdded xk yk c = do
    i <- runCircuit xk
    j <- runCircuit yk
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)
