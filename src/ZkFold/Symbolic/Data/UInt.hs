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
import           Control.Monad.State                (StateT (..))
import           Data.Foldable                      (foldr, foldrM, for_)
import           Data.Functor                       ((<$>))
import           Data.Kind                          (Type)
import           Data.List                          (unfoldr, zip)
import           Data.Map                           (fromList, (!))
import           Data.Traversable                   (for, traverse)
import           Data.Tuple                         (swap)
import qualified Data.Zip                           as Z
import           GHC.Generics                       (Generic, Par1 (..))
import           GHC.Natural                        (naturalFromInteger)
import           Prelude                            (Integer, error, flip, otherwise, return, type (~), ($), (++), (.),
                                                     (<>), (>>=))
import qualified Prelude                            as Haskell
import           Test.QuickCheck                    (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field    (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector            as V
import           ZkFold.Base.Data.Vector            (Vector (..))
import           ZkFold.Prelude                     (drop, length, replicate, replicateA)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class         (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Interpreter        (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit       (MonadCircuit, constraint, newAssigned)

-- TODO (Issue #18): hide this constructor
newtype UInt (n :: Natural) (r :: RegisterSize) (context :: (Type -> Type) -> Type) = UInt (context (Vector (NumberOfRegisters (BaseField context) n r)))

deriving instance Generic (UInt n r context)
deriving instance (NFData (context (Vector (NumberOfRegisters (BaseField context) n r)))) => NFData (UInt n r context)
deriving instance (Haskell.Eq (context (Vector (NumberOfRegisters (BaseField context) n r)))) => Haskell.Eq (UInt n r context)
deriving instance (Haskell.Show (BaseField context), Haskell.Show (context (Vector (NumberOfRegisters (BaseField context) n r)))) => Haskell.Show (UInt n r context)
deriving newtype instance SymbolicData (UInt n r c)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => FromConstant Natural (UInt n r c) where
    fromConstant c = UInt . embed @c $ naturalToVector @c @n @r c

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => FromConstant Integer (UInt n r c) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Symbolic c, KnownNat n, KnownRegisterSize r, FromConstant a (UInt n r c), MultiplicativeMonoid a) => Scale a (UInt n r c)

instance MultiplicativeMonoid (UInt n r c) => Exponent (UInt n r c) Natural where
    (^) = natPow

cast :: forall a n r . (Arithmetic a, KnownNat n, KnownRegisterSize r) => Natural -> ([Natural], Natural, [Natural])
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
instance (Symbolic (Interpreter (Zp p)), KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter (Zp p))) Natural where
    toConstant (UInt (Interpreter xs)) = vectorToNatural xs (registerSize @(Zp p) @n @r)

instance (Symbolic (Interpreter (Zp p)), KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter (Zp p))) Integer where
    toConstant = Haskell.fromIntegral @Natural . toConstant

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => MultiplicativeMonoid (UInt n r c) where
    one = fromConstant (1 :: Natural)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Semiring (UInt n r c)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Arbitrary (UInt n r c) where
    arbitrary = do
        lo <- replicateA (numberOfRegisters @(BaseField c) @n @r -! 1) (toss $ registerSize @(BaseField c) @n @r)
        hi <- toss (highRegisterSize @(BaseField c) @n @r)
        return $ UInt $ embed $ V.unsafeToVector (lo <> [hi])
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Iso (ByteString n c) (UInt n r c) where
    from (ByteString b) = UInt $ symbolicF b (naturalToVector @c @n @r . Haskell.foldl (\y p -> toConstant p + 2 * y) 0) solve
        where
            solve :: forall i m. MonadCircuit i (BaseField c) m => Vector n i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve bits = do
                let bsBits = V.fromVector bits
                V.unsafeToVector . Haskell.reverse <$> fromBits (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) bsBits

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Iso (UInt n r c) (ByteString n c) where
    from (UInt u) =  ByteString $ symbolicF u (\ v ->  V.unsafeToVector $ fromConstant <$> toBsBits (vectorToNatural v (registerSize @(BaseField c) @n @r)) (value @n)) solve
        where
            solve :: forall i m. MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector n i)
            solve ui = do
                let regs = V.fromVector ui
                V.unsafeToVector <$> toBits (Haskell.reverse regs) (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r)

-- --------------------------------------------------------------------------------

instance
    ( Symbolic c
    , KnownNat n
    , KnownNat k
    , KnownRegisterSize r
    , n <= k
    ) => Extend (UInt n r c) (UInt k r c) where
    extend (UInt x) = UInt $ symbolicF x (\l ->  naturalToVector @c @k @r (vectorToNatural l (registerSize @(BaseField c) @n @r))) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) k r) i)
            solve xv = do
                let regs = V.fromVector xv
                zeros <- replicateA (value @k -! (value @n)) (newAssigned (Haskell.const zero))
                bsBits <- toBits (Haskell.reverse regs) (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r)
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
    ( Symbolic c
    , KnownNat n
    , KnownNat r
    , KnownRegisterSize rs
    , r ~ NumberOfRegisters (BaseField c) n rs
    , NFData (c (Vector r))
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

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Ord (Bool c) (UInt n r c) where
    x <= y = y >= x

    x <  y = y > x

    u1 >= u2 =
        let ByteString rs1 = from u1 :: ByteString n c
            ByteString rs2 = from u2 :: ByteString n c
         in bitwiseGE rs1 rs2

    u1 > u2 =
        let ByteString rs1 = from u1 :: ByteString n c
            ByteString rs2 = from u2 :: ByteString n c
        in bitwiseGT rs1 rs2

    max x y = bool @(Bool c) x y $ x < y

    min x y = bool @(Bool c) x y $ x > y


instance (Symbolic c, KnownNat n, KnownRegisterSize r) => AdditiveSemigroup (UInt n r c) where
    UInt xc + UInt yc = UInt $ symbolic2F xc yc (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) + vectorToNatural v (registerSize @(BaseField c) @n @r)) solve
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

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => AdditiveMonoid (UInt n r c) where
    zero = fromConstant (0:: Natural)

instance
    (Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => AdditiveGroup (UInt n r c) where

    UInt x - UInt y = UInt $ symbolic2F x y (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) + 2 ^ (value @n) -! vectorToNatural v (registerSize @(BaseField c) @n @r) ) solve
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

    negate :: UInt n r c -> UInt n r c
    negate (UInt x) =  UInt $ symbolicF x (\v ->  naturalToVector @c @n @r $ (2 ^ (value @n) ) -! vectorToNatural v (registerSize @(BaseField c) @n @r)) solve
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
                (zs, _) <- flip runStateT j $ traverse StateT (Haskell.zipWith negateN ns xs)
                return $ V.unsafeToVector zs

            negateN :: MonadCircuit i (BaseField c) m => Natural -> i -> i -> m (i, i)
            negateN n i b = do
                r <- newAssigned (\v -> fromConstant n - v i + v b)
                splitExpansion (registerSize @(BaseField c) @n @r) 1 r


instance (Symbolic c, KnownNat n, KnownRegisterSize rs) => MultiplicativeSemigroup (UInt n rs c) where
    UInt x * UInt y = UInt $ symbolic2F x y (\u v -> naturalToVector @c @n @rs $ vectorToNatural u (registerSize @(BaseField c) @n @rs) * vectorToNatural v (registerSize @(BaseField c) @n @rs)) solve
        where
            solve :: forall i m. (MonadCircuit i (BaseField c) m) => Vector (NumberOfRegisters (BaseField c) n rs) i -> Vector (NumberOfRegisters (BaseField c) n rs) i -> m (Vector (NumberOfRegisters (BaseField c) n rs) i)
            solve xv yv = do
                case V.fromVector $ Z.zip xv yv of
                  []              -> return $ V.unsafeToVector []
                  [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)

            solve1 :: forall i m. (MonadCircuit i (BaseField c) m) => i -> i -> m [i]
            solve1 i j = do
                (z, _) <- newAssigned (\v -> v i * v j) >>= splitExpansion (highRegisterSize @(BaseField c) @n @rs) (maxOverflow @(BaseField c) @n @rs)
                return [z]

            solveN :: forall i m. (MonadCircuit i (BaseField c) m) => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @(BaseField c) @n @rs
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @(BaseField c) @n @rs) (registerSize @(BaseField c) @n @rs) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @(BaseField c) @n @rs) (maxOverflow @(BaseField c) @n @rs) s
                -- high register
                p'0 <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v k' + v l)) c' [0 .. r -! 1]
                (p', _) <- splitExpansion (highRegisterSize @(BaseField c) @n @rs) (maxOverflow @(BaseField c) @n @rs) p'0
                return (p : ps <> [p'])

instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Ring (UInt n r c)

deriving via (Structural (UInt n rs c))
         instance (Symbolic c) =>
         Eq (Bool c) (UInt n rs c)

--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (Symbolic c, KnownNat n, KnownRegisterSize rs) => StrictConv Natural (UInt n rs c) where
    strictConv n = case cast @(BaseField c) @n @rs n of
        (lo, hi, []) -> UInt $ embed $ V.unsafeToVector $ fromConstant <$> (lo <> [hi])
        _            -> error "strictConv: overflow"

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => StrictConv (Zp p) (UInt n r c) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => StrictConv (c Par1) (UInt n r c) where
    strictConv a = UInt $ symbolicF a (\p -> V.unsafeToVector [unPar1 p]) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Par1 i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv = do
                let i = unPar1 xv
                    len = Haskell.min (getNatural @n) (numberOfBits @(BaseField c))
                bits <- Haskell.reverse <$> expansion len i
                V.unsafeToVector <$> fromBits (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) bits


class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => StrictNum (UInt n r c) where
    strictAdd (UInt x) (UInt y) = UInt $ symbolic2F x y (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) + vectorToNatural v (registerSize @(BaseField c) @n @r)) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv yv = do
                j <- newAssigned (Haskell.const zero)
                let xs = V.fromVector xv
                    ys = V.fromVector yv
                    z    = Haskell.last xs
                    w    = Haskell.last ys
                    midx = Haskell.init xs
                    midy = Haskell.init ys
                (zs, c) <- flip runStateT j $ traverse StateT $
                    Haskell.zipWith (fullAdder $ registerSize @(BaseField c) @n @r) midx midy
                k <- fullAdded z w c
                (ks, _) <- splitExpansion (highRegisterSize @(BaseField c) @n @r) 1 k
                return $ V.unsafeToVector (zs ++ [ks])


    strictSub (UInt x) (UInt y) = UInt $ symbolic2F x y (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) -! vectorToNatural v (registerSize @(BaseField c) @n @r)) solve
        where
            t :: BaseField c
            t = (one + one) ^ registerSize @(BaseField c) @n @r - one

            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv yv = do
                case V.fromVector $ Z.zip xv yv of
                  []              -> return $ V.unsafeToVector []
                  [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadCircuit i (BaseField c) m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned (\v -> v i - v j)
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) z
                return [z]

            solveN :: MonadCircuit i (BaseField c) m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @(BaseField c) @n @r) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith fullSub is js)
                k' <- newAssigned (\v -> v i' - v j')
                s' <- newAssigned (\v -> v k' + v b - one)
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) s'
                return (k : zs <> [s'])


            fullSub :: MonadCircuit i (BaseField c) m => i -> i -> i -> m (i, i)
            fullSub xk yk b = do
                k <- newAssigned (\v -> v xk - v yk)
                s <- newAssigned (\v -> v k + v b + fromConstant t)
                splitExpansion (registerSize @(BaseField c) @n @r) 1 s

    strictMul (UInt x) (UInt y) = UInt $ symbolic2F x y (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) * vectorToNatural v (registerSize @(BaseField c) @n @r)) solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> Vector (NumberOfRegisters (BaseField c) n r) i -> m (Vector (NumberOfRegisters (BaseField c) n r) i)
            solve xv yv = do
                case V.fromVector $ Z.zip xv yv of
                  []              -> return $ V.unsafeToVector []
                  [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)

            solve1 :: MonadCircuit i (BaseField c) m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned $ \v -> v i * v j
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) z
                return [z]

            solveN :: MonadCircuit i (BaseField c) m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @(BaseField c) @n @r
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @(BaseField c) @n @r) (maxOverflow @(BaseField c) @n @r) s
                -- high register
                p' <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v l + v k')) c' [0 .. r -! 1]
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) p'
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

naturalToVector :: forall c n r . (Symbolic c, KnownNat n, KnownRegisterSize r) => Natural -> Vector (NumberOfRegisters (BaseField c) n r) (BaseField c)
naturalToVector c = let (lo, hi, _) = cast @(BaseField c) @n @r . (`Haskell.mod` (2 ^ getNatural @n)) $ c
    in V.unsafeToVector $ (fromConstant <$> lo) <> [fromConstant hi]


vectorToNatural :: (ToConstant a Natural) => Vector n a -> Natural -> Natural
vectorToNatural v n = foldr (\l r -> fromConstant l  + b * r) 0 vs where
    vs = Haskell.map toConstant $ V.fromVector v :: [Natural]
    b = 2 ^ n
