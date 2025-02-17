{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE NoDeriveAnyClass     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Data.UInt (
    StrictConv(..),
    StrictNum(..),
    UInt(..),
    OrdWord,
    toConstant,
    toNative,
    asWords,
    expMod,
    eea,
    natural,
    register
) where

import           Control.Applicative               (Applicative (..))
import           Control.DeepSeq
import           Control.Monad.State               (StateT (..))
import           Data.Aeson                        hiding (Bool)
import           Data.Foldable                     (Foldable (toList), foldlM, foldr, foldrM, for_)
import           Data.Function                     (on)
import           Data.Functor                      (Functor (..), (<$>))
import           Data.Functor.Rep                  (Representable (..))
import           Data.Kind                         (Type)
import           Data.List                         (unfoldr, zip)
import           Data.Map                          (fromList, (!))
import           Data.Traversable                  (for, traverse)
import           Data.Tuple                        (swap)
import qualified Data.Zip                          as Z
import           GHC.Generics                      (Generic, Par1 (..), (:*:) (..))
import           GHC.Natural                       (naturalFromInteger)
import           Prelude                           (Integer, const, error, flip, otherwise, return, type (~), ($), (++),
                                                    (.), (<>), (>>=))
import qualified Prelude                           as Haskell
import           Test.QuickCheck                   (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class   hiding (Euclidean (..))
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Control.HApplicative  (HApplicative (..))
import           ZkFold.Base.Data.HFunctor         (HFunctor (..))
import           ZkFold.Base.Data.Product          (fstP, sndP)
import qualified ZkFold.Base.Data.Vector           as V
import           ZkFold.Base.Data.Vector           (Vector (..))
import           ZkFold.Prelude                    (length, replicate, replicateA)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class        (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (..))
import           ZkFold.Symbolic.Data.Input        (SymbolicInput, isValid)
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Interpreter       (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit      (MonadCircuit (..), ResidueField (..), Witness (..), constraint,
                                                    newAssigned)


-- TODO (Issue #18): hide this constructor
newtype UInt (n :: Natural) (r :: RegisterSize) (context :: (Type -> Type) -> Type) = UInt (context (Vector (NumberOfRegisters (BaseField context) n r)))

deriving instance Generic (UInt n r context)
deriving instance (NFData (context (Vector (NumberOfRegisters (BaseField context) n r)))) => NFData (UInt n r context)
deriving instance (Haskell.Eq (context (Vector (NumberOfRegisters (BaseField context) n r)))) => Haskell.Eq (UInt n r context)
deriving instance (Haskell.Show (BaseField context), Haskell.Show (context (Vector (NumberOfRegisters (BaseField context) n r)))) => Haskell.Show (UInt n r context)
deriving newtype instance (KnownRegisters c n r, Symbolic c) => SymbolicData (UInt n r c)
deriving newtype instance (KnownRegisters c n r, Symbolic c) => Conditional (Bool c) (UInt n r c)
deriving newtype instance (KnownRegisters c n r, Symbolic c) => Eq (UInt n r c)

toNative ::
  forall n r c a.
  (Symbolic c, KnownNat n, KnownRegisterSize r, BaseField c ~ a) =>
  (KnownNat (GetRegisterSize a n r)) =>
  UInt n r c -> FieldElement c
toNative (UInt rs) = FieldElement $ symbolicF rs
  (Par1 . fromConstant . (`vectorToNatural` registerSize @(BaseField c) @n @r))
  (fmap Par1 . hornerW @(GetRegisterSize a n r) . toList)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => FromConstant Natural (UInt n r c) where
    fromConstant c = UInt . embed @c $ naturalToVector @c @n @r c

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => FromConstant Integer (UInt n r c) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Scale Natural (UInt n r c)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Scale Integer (UInt n r c)

instance MultiplicativeMonoid (UInt n r c) => Exponent (UInt n r c) Natural where
    (^) = natPow

-- | @expMod n pow modulus@ calculates @n^pow % modulus@ where all values are arithmetised
--
expMod
    :: forall c n p m r
    .  Symbolic c
    => KnownRegisterSize r
    => KnownNat p
    => KnownNat n
    => KnownNat m
    => KnownNat (2 * m)
    => KnownRegisters c (2 * m) r
    => KnownNat (Ceil (GetRegisterSize (BaseField c) (2 * m) r) OrdWord)
    => NFData (c (Vector (NumberOfRegisters (BaseField c) (2 * m) r)))
    => UInt n r c
    -> UInt p r c
    -> UInt m r c
    -> UInt m r c
expMod n pow modulus = resize result
    where
        bits :: ByteString p c
        bits = from pow

        m' :: UInt (2 * m) r c
        m' = resize modulus

        n' :: UInt (2 * m) r c
        n' = resize n `mod` m'

        result :: UInt (2 * m) r c
        result = bitsPow (value @p) bits one n' m'

bitsPow
    :: forall c n p r
    .  Symbolic c
    => KnownRegisterSize r
    => KnownNat n
    => KnownNat p
    => KnownRegisters c n r
    => KnownNat (Ceil (GetRegisterSize (BaseField c) n r) OrdWord)
    => NFData (c (Vector (NumberOfRegisters (BaseField c) n r)))
    => Natural
    -> ByteString p c
    -> UInt n r c
    -> UInt n r c
    -> UInt n r c
    -> UInt n r c
bitsPow 0 _ res _ _ = res
bitsPow b bits res n m = bitsPow (b -! 1) bits newRes sq m
    where
        sq = (n * n) `mod` m
        newRes = force $ ifThenElse (isSet bits (b -! 1)) ((res * n) `mod` m) res


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
    => SemiEuclidean (UInt n r c)
    => KnownNat n
    => KnownRegisters c n r
    => AdditiveGroup (UInt n r c)
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

instance (Symbolic (Interpreter a), KnownNat n, KnownRegisterSize r) => ToConstant (UInt n r (Interpreter a)) where
    type Const (UInt n r (Interpreter a)) = Natural
    toConstant (UInt (Interpreter xs)) = vectorToNatural xs (registerSize @a @n @r)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => MultiplicativeMonoid (UInt n r c) where
    one = fromConstant (1 :: Natural)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Semiring (UInt n r c)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Arbitrary (UInt n r c) where
    arbitrary
      | value @n == 0 = return zero
      | otherwise     = do
        lo <- replicateA (numberOfRegisters @(BaseField c) @n @r -! 1) (toss $ registerSize @(BaseField c) @n @r)
        hi <- toss (highRegisterSize @(BaseField c) @n @r)
        return $ UInt $ embed $ V.unsafeToVector (lo <> [hi])
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Iso (ByteString n c) (UInt n r c) where
    from (ByteString b)
      | value @n == 0 = zero
      | otherwise     = UInt $ symbolicF b
        (naturalToVector @c @n @r . Haskell.foldl (\y p -> toConstant p + 2 * y) 0)
        (\bits -> do
            let bsBits = V.fromVector bits
            V.unsafeToVector . Haskell.reverse <$> fromBits (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) bsBits
        )

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Iso (UInt n r c) (ByteString n c) where
    from (UInt u)
      | value @n == 0 = ByteString $ embed $ V.unsafeToVector []
      | otherwise     = ByteString $ symbolicF u
        (\v -> V.unsafeToVector $ fromConstant <$> toBsBits (vectorToNatural v (registerSize @(BaseField c) @n @r)) (value @n))
        (\ui -> do
            let regs = V.fromVector ui
            V.unsafeToVector <$> toBits (Haskell.reverse regs) (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r)
        )

instance (Symbolic c, KnownRegisterSize r, NumberOfBits (BaseField c) ~ n) => Iso (FieldElement c) (UInt n r c) where
  from a = from (from a :: ByteString n c)

instance (Symbolic c, KnownRegisterSize r, NumberOfBits (BaseField c) ~ n) => Iso (UInt n r c) (FieldElement c) where
  from a = from (from a :: ByteString n c)

-- --------------------------------------------------------------------------------

instance
    ( Symbolic c
    , KnownNat n
    , KnownNat k
    , KnownRegisterSize r
    ) => Resize (UInt n r c) (UInt k r c) where
    resize (UInt bits)
      | value @n == 0 = zero
      | value @k == 0 = zero
      | otherwise     = UInt $ symbolicF bits
        (\l -> naturalToVector @c @k @r (vectorToNatural l (registerSize @(BaseField c) @n @r)))
        (\v -> do
            let regs = V.fromVector v
                ns = replicate (numberOfRegisters @(BaseField c) @n @r -! 1) n ++ [highRegisterSize @(BaseField c) @n @r]
                ks = replicate (numberOfRegisters @(BaseField c) @k @r -! 1) k ++ [highRegisterSize @(BaseField c) @k @r]
                zs = zip ns regs

            resZ <- helper zs ks
            let (_, res) = Haskell.unzip resZ
            return $ V.unsafeToVector res
        )
        where
            n = registerSize @(BaseField c) @n @r
            k = registerSize @(BaseField c) @k @r

            helper :: MonadCircuit i (BaseField c) w m => [(Natural, i)] -> [Natural] -> m [(Natural, i)]
            helper _ [] = return []
            helper [] (a:as) = do
                ([(a, fromConstant @(BaseField c) zero)] <> ) Haskell.<$> helper [] as
            helper ((xN, xI) : xs) acc@(a:as)
                | xN > a = do
                        (l, h) <- splitExpansion a (xN -! a) xI
                        ([(a, l)] <> ) Haskell.<$> helper ((xN -! a, h) : xs) as
                | xN == a = ([(a, xI)] <> ) Haskell.<$> helper xs as
                | otherwise = case xs of
                    [] -> ([(xN, xI)] <> ) Haskell.<$> helper [] as
                    ((yN, yI) : ys) -> do
                        let newN = xN + yN
                        newI <- newAssigned (\j -> j xI + scale ((2 :: Natural) ^ xN) (j yI))
                        helper ((newN, newI) : ys) acc

-- | "natural" value from vector of registers.
natural ::
  forall c n r i.
  (Symbolic c, KnownNat n, KnownRegisterSize r, Witness i (WitnessField c)) =>
  Vector (NumberOfRegisters (BaseField c) n r) i -> IntegralOf (WitnessField c)
natural =
  foldr
    (\i c -> toIntegral (at i :: WitnessField c) + fromConstant base * c)
    zero
  where
    base :: Natural
    base = 2 ^ registerSize @(BaseField c) @n @r

-- | @register n i@ returns @i@-th register of @n@.
register ::
  forall c n r. (Symbolic c, KnownNat n, KnownRegisterSize r) =>
  IntegralOf (WitnessField c) ->
  Zp (NumberOfRegisters (BaseField c) n r) -> WitnessField c
register c i =
  fromIntegral ((c `div` fromConstant (2 ^ shift :: Natural)) `mod` base)
  where
    rs = registerSize @(BaseField c) @n @r
    base = fromConstant (2 ^ rs :: Natural)
    shift = Haskell.fromIntegral (toConstant i) * rs

instance ( Symbolic c, KnownNat n, KnownRegisterSize r
         , KnownRegisters c n r
         , regSize ~ GetRegisterSize (BaseField c) n r
         , KnownNat (Ceil regSize OrdWord)
         ) => SemiEuclidean (UInt n r c) where
    divMod num@(UInt nm) den@(UInt dn) =
      (UInt $ hmap fstP circuit, UInt $ hmap sndP circuit)
      where

        -- | Computes unconstrained registers of @div@ and @mod@.
        source = symbolic2F nm dn
          (\n d ->
            let r = registerSize @(BaseField c) @n @r
                n' = vectorToNatural n r
                d' = vectorToNatural d r
            in naturalToVector @c @n @r (n' `div` d')
                :*: naturalToVector @c @n @r (n' `mod` d'))
          \n d -> (liftA2 (:*:) `on` traverse unconstrained)
            (tabulate $ register @c @n @r (natural @c @n @r n `div` natural @c @n @r d))
            (tabulate $ register @c @n @r (natural @c @n @r n `mod` natural @c @n @r d))

        -- | Unconstrained @div@ part.
        dv = hmap fstP source

        -- | Unconstrained @mod@ part.
        md = hmap sndP source

        -- | divMod first constraint: @numerator = denominator * div + mod@.
        -- This should always be true.
        Bool eq = den * UInt dv + UInt md == num

        -- | divMod second constraint: @0 <= mod < denominator@.
        -- This should always be true.
        Bool lt = UInt md < den

        -- | Computes properly constrained registers of @div@ and @mod@.
        circuit = fromCircuit3F eq lt (dv `hpair` md) \(Par1 e) (Par1 l) dm -> do
          constraint (($ e) - one)
          constraint (($ l) - one)
          return dm

asWords
    :: forall wordSize regSize ctx k
    .  Symbolic ctx
    => KnownNat (Ceil regSize wordSize)
    => KnownNat wordSize
    => ctx (Vector k)                           -- @k@ registers of size up to @regSize@
    -> ctx (Vector (k * Ceil regSize wordSize)) -- @k * wordsPerReg@ registers of size @wordSize@
asWords v = fromCircuitF v $ \regs -> do
    words <- Haskell.mapM (expansionW @wordSize wordsPerReg) regs
    Haskell.pure $ V.reverse . V.unsafeToVector . Haskell.concat . V.fromVector $ words
  where
      wordsPerReg :: Natural
      wordsPerReg = value @(Ceil regSize wordSize)

-- | Word size in bits used in comparisons. Subject to change
type OrdWord = 16

instance ( Symbolic c, KnownNat n, KnownRegisterSize r
         , KnownRegisters c n r
         , regSize ~ GetRegisterSize (BaseField c) n r
         , KnownNat (Ceil regSize OrdWord)
         ) => Ord (Bool c) (UInt n r c) where
    x <= y = y >= x

    x <  y = y > x

    (UInt u1) >= (UInt u2) =
        let w1 = asWords @OrdWord @regSize u1
            w2 = asWords @OrdWord @regSize u2
         in bitwiseGE @OrdWord w1 w2

    (UInt u1) > (UInt u2) =
        let w1 = asWords @OrdWord @regSize u1
            w2 = asWords @OrdWord @regSize u2
         in bitwiseGT @OrdWord w1 w2

    max x y = bool @(Bool c) x y $ x < y

    min x y = bool @(Bool c) x y $ x > y

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => AdditiveSemigroup (UInt n r c) where
    UInt xc + UInt yc
      | value @n == 0 = zero
      | otherwise     = UInt $ symbolic2F xc yc
        (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) + vectorToNatural v (registerSize @(BaseField c) @n @r))
        (\xv yv -> do
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
        )

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => AdditiveMonoid (UInt n r c) where
    zero = fromConstant (0:: Natural)

instance
    (Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => AdditiveGroup (UInt n r c) where

    UInt x - UInt y = UInt $ symbolic2F x y
        (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) + 2 ^ (value @n) -! vectorToNatural v (registerSize @(BaseField c) @n @r))
        (\xv yv -> do
            let is = V.fromVector xv
                js = V.fromVector yv
            case Z.zip is js of
                []              -> return $ V.unsafeToVector []
                [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                       (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                    in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)
        )
        where
            t :: BaseField c
            t = (one + one) ^ registerSize @(BaseField c) @n @r

            solve1 :: MonadCircuit i (BaseField c) w m => i -> i -> m [i]
            solve1 i j = do
                z0 <- newAssigned (\v -> v i - v j + fromConstant t)
                (z, _) <- splitExpansion (highRegisterSize @(BaseField c) @n @r) 1 z0
                return [z]

            solveN :: MonadCircuit i (BaseField c) w m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                s <- newAssigned (\v -> v i - v j + fromConstant t)
                let r = registerSize @(BaseField c) @n @r
                (k, b0) <- splitExpansion r 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith (fullSub r) is js)
                d <- newAssigned (\v -> v i' - v j')
                s'0 <- newAssigned (\v -> v d + v b + fromConstant (2 ^ highRegisterSize @(BaseField c) @n @r -! 1 :: Natural))
                (s', _) <- splitExpansion (highRegisterSize @(BaseField c) @n @r) 1 s'0
                return (k : zs <> [s'])

    negate :: UInt n r c -> UInt n r c
    negate (UInt x) = UInt $ symbolicF x
        (\v -> naturalToVector @c @n @r $ (2 ^ value @n) -! vectorToNatural v (registerSize @(BaseField c) @n @r))
        (\xv -> do
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
        )
        where
            negateN :: MonadCircuit i (BaseField c) w m => Natural -> i -> i -> m (i, i)
            negateN n i b = do
                r <- newAssigned (\v -> fromConstant n - v i + v b)
                splitExpansion (registerSize @(BaseField c) @n @r) 1 r


instance (Symbolic c, KnownNat n, KnownRegisterSize rs) => MultiplicativeSemigroup (UInt n rs c) where
    UInt x * UInt y = UInt $ symbolic2F x y
        (\u v -> naturalToVector @c @n @rs $ vectorToNatural u (registerSize @(BaseField c) @n @rs) * vectorToNatural v (registerSize @(BaseField c) @n @rs))
        (\xv yv -> do
            case V.fromVector $ Z.zip xv yv of
              []              -> return $ V.unsafeToVector []
              [(i, j)]        -> V.unsafeToVector <$> solve1 i j
              ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                     (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                  in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)
        )
        where
            solve1 :: forall i w m. MonadCircuit i (BaseField c) w m => i -> i -> m [i]
            solve1 i j = do
                (z, _) <- newAssigned (\v -> v i * v j) >>= splitExpansion (highRegisterSize @(BaseField c) @n @rs) (maxOverflow @(BaseField c) @n @rs)
                return [z]

            solveN :: forall i w m. MonadCircuit i (BaseField c) w m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
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
                let highOverflow = registerSize @(BaseField c) @n @rs + maxOverflow @(BaseField c) @n @rs -! highRegisterSize @(BaseField c) @n @rs
                (p', _) <- splitExpansion (highRegisterSize @(BaseField c) @n @rs) highOverflow p'0
                return (p : ps <> [p'])

instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Ring (UInt n r c)

--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (Symbolic c, KnownNat n, KnownRegisterSize rs) => StrictConv Natural (UInt n rs c) where
    strictConv n
      | value @n == 0 = zero
      | otherwise     = case cast @(BaseField c) @n @rs n of
        (lo, hi, []) -> UInt $ embed $ V.unsafeToVector $ fromConstant <$> (lo <> [hi])
        _            -> error "strictConv: overflow"

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => StrictConv (Zp p) (UInt n r c) where
    strictConv = strictConv . toConstant

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => StrictConv (c Par1) (UInt n r c) where
    strictConv a = UInt $ symbolicF a (\p -> V.unsafeToVector [unPar1 p]) (\xv -> do
        let i = unPar1 xv
            len = Haskell.min (getNatural @n) (numberOfBits @(BaseField c))
        bits <- Haskell.reverse <$> expansion len i
        V.unsafeToVector <$> fromBits (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) bits)


class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => StrictNum (UInt n r c) where
    strictAdd (UInt x) (UInt y)
      | value @n == 0 = zero
      | otherwise     = UInt $ symbolic2F x y
        (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) + vectorToNatural v (registerSize @(BaseField c) @n @r))
        (\xv yv -> do
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
        )

    strictSub (UInt x) (UInt y) = UInt $ symbolic2F x y
        (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) -! vectorToNatural v (registerSize @(BaseField c) @n @r))
        (\xv yv -> do
            case V.fromVector $ Z.zip xv yv of
              []              -> return $ V.unsafeToVector []
              [(i, j)]        -> V.unsafeToVector <$> solve1 i j
              ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                     (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                  in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)
        )
        where
            t :: BaseField c
            t = (one + one) ^ registerSize @(BaseField c) @n @r - one

            solve1 :: MonadCircuit i (BaseField c) w m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned (\v -> v i - v j)
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) z
                return [z]

            solveN :: MonadCircuit i (BaseField c) w m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
            solveN (i, j) (is, js) (i', j') = do
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                let r = registerSize @(BaseField c) @n @r
                (k, b0) <- splitExpansion r 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (Haskell.zipWith (fullSub r) is js)
                k' <- newAssigned (\v -> v i' - v j')
                s' <- newAssigned (\v -> v k' + v b - one)
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) s'
                return (k : zs <> [s'])

    strictMul (UInt x) (UInt y) = UInt $ symbolic2F x y
        (\u v -> naturalToVector @c @n @r $ vectorToNatural u (registerSize @(BaseField c) @n @r) * vectorToNatural v (registerSize @(BaseField c) @n @r))
        (\xv yv -> do
                case V.fromVector $ Z.zip xv yv of
                  []              -> return $ V.unsafeToVector []
                  [(i, j)]        -> V.unsafeToVector <$> solve1 i j
                  ((i, j) : rest) -> let (z, w) = Haskell.last rest
                                         (ris, rjs) = Haskell.unzip $ Haskell.init rest
                                      in V.unsafeToVector <$> solveN (i, j) (ris, rjs) (z, w)
        )
        where
            solve1 :: MonadCircuit i (BaseField c) w m => i -> i -> m [i]
            solve1 i j = do
                z <- newAssigned $ \v -> v i * v j
                _ <- expansion (highRegisterSize @(BaseField c) @n @r) z
                return [z]

            solveN :: MonadCircuit i (BaseField c) w m => (i, i) -> ([i], [i]) -> (i, i) -> m [i]
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

instance
  ( Symbolic c
  , KnownNat n
  , KnownRegisterSize r
  , KnownRegisters c n r
  ) => SymbolicInput (UInt n r c) where

    isValid (UInt bits)
      | value @n == 0 = true
      | otherwise     = Bool $ fromCircuitF bits $ \v -> do
        let vs = V.fromVector v
        bs <- toBits (Haskell.reverse vs) (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r)
        ys <- Haskell.reverse <$> fromBits (highRegisterSize @(BaseField c) @n @r) (registerSize @(BaseField c) @n @r) bs
        difference <- for (zip vs ys) $ \(i, j) -> newAssigned (\w -> w i - w j)
        isZeros <- for difference $ isZero . Par1
        case isZeros of
            []       -> Par1 <$> newAssigned (const one)
            (z : zs) -> foldlM (\(Par1 v1) (Par1 v2) -> Par1 <$> newAssigned (($ v1) * ($ v2))) z zs

--------------------------------------------------------------------------------

fullAdder :: (Arithmetic a, MonadCircuit i a w m) => Natural -> i -> i -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadCircuit i a w m => i -> i -> i -> m i
fullAdded i j c = do
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)

fullSub :: (Arithmetic a, MonadCircuit i a w m) => Natural -> i -> i -> i -> m (i, i)
fullSub r xk yk b = do
    d <- newAssigned (\v -> v xk - v yk)
    s <- newAssigned (\v -> v d + v b + (one + one) ^ r - one)
    splitExpansion r 1 s

naturalToVector :: forall c n r . (Symbolic c, KnownNat n, KnownRegisterSize r) => Natural -> Vector (NumberOfRegisters (BaseField c) n r) (BaseField c)
naturalToVector c
  | value @n == 0 = V.unsafeToVector []
  | otherwise     = let (lo, hi, _) = cast @(BaseField c) @n @r . (`Haskell.mod` (2 ^ getNatural @n)) $ c
                     in V.unsafeToVector $ (fromConstant <$> lo) <> [fromConstant hi]

vectorToNatural :: (ToConstant a, Const a ~ Natural) => Vector n a -> Natural -> Natural
vectorToNatural v n = foldr (\l r -> fromConstant l  + b * r) 0 vs where
    vs = Haskell.map toConstant $ V.fromVector v :: [Natural]
    b = 2 ^ n

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => FromJSON (UInt n r c) where
    parseJSON = Haskell.fmap strictConv . parseJSON @Natural

instance (Symbolic (Interpreter (Zp p)), KnownNat n, KnownRegisterSize r) => ToJSON (UInt n r (Interpreter (Zp p))) where
    toJSON = toJSON . toConstant
