{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module ZkFold.Symbolic.Data.FFA0 where
  -- (FFA0 (..), Size, coprimesDownFrom, coprimes)

import           Control.Applicative              (pure)
import           Control.DeepSeq                  (NFData, force)
import           Control.Monad                    (Monad, forM, return, (>>=))
import           Data.Foldable                    (any, foldlM)
import           Data.Function                    (const, ($), (.))
import           Data.Functor                     (fmap, (<$>))
import           Data.List                        (dropWhile, (++))
import           Data.Ratio                       ((%))
import           Data.Traversable                 (for, traverse)
import           Data.Tuple                       (fst, snd, uncurry)
import           Data.Zip                         (zipWith)
import           Prelude                          (Integer, error, undefined, Int)
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp, inv)
import qualified ZkFold.Base.Algebra.Basic.Field  as PrimeField
import qualified Data.Vector                      as V
import qualified Data.Foldable                    as F
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Utils           (zipWithM)
import           ZkFold.Base.Data.Vector
import           ZkFold.Prelude                   (iterateM, length)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators (expansionW, log2, maxBitsPerFieldElement, splitExpansion)
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Input
import           ZkFold.Symbolic.Data.Ord         (blueprintGE)
import           ZkFold.Symbolic.Interpreter
import           ZkFold.Symbolic.MonadCircuit     (MonadCircuit, newAssigned)
import Data.Bits (Bits(..))
import qualified Prelude as P

type Size = 7

-- | Foreign-field arithmetic based on https://cr.yp.to/papers/mmecrt.pdf
newtype FFA0 (p :: Natural) c = FFA0 (c (Vector Size))

deriving newtype instance Symbolic c => SymbolicData (FFA0 p c)
deriving newtype instance NFData (c (Vector Size)) => NFData (FFA0 p c)
deriving newtype instance Haskell.Show (c (Vector Size)) => Haskell.Show (FFA0 p c)

coprimesDownFrom :: KnownNat n => Natural -> Vector n Natural
coprimesDownFrom n = unfold (uncurry step) ([], [n,n-!1..0])
  where
    step ans xs =
      case dropWhile (\x -> any ((Haskell./= 1) . Haskell.gcd x) ans) xs of
        []      -> error "no options left"
        (x:xs') -> (x, (ans ++ [x], xs'))

coprimes :: forall a. Finite a => Vector Size Natural
coprimes = coprimesDownFrom @Size $ 2 ^ (maxBitsPerFieldElement @a `div` 2)

sigma :: Natural
sigma = Haskell.ceiling (log2 $ value @Size) + 1 :: Natural

mprod0 :: forall a. Finite a => Natural
mprod0 = product (coprimes @a)

mprod :: forall a p . (Finite a, KnownNat p) => Natural
mprod = mprod0 @a `mod` value @p

mis0 :: forall a. Finite a => Vector Size Natural
mis0 = let m = mprod0 @a in (m `div`) <$> (coprimes @a)

mis :: forall a p. (Finite a, KnownNat p) => Vector Size Natural
mis = (`mod` value @p) <$> mis0 @a

minv :: forall a. Finite a => Vector Size Natural
minv = zipWith (\x p -> fromConstant x `inv` p) (mis0 @a) (coprimes @a)

wordExpansion :: forall r. KnownNat r => Natural -> [Natural]
wordExpansion 0 = []
wordExpansion x = (x `mod` wordSize) : wordExpansion @r (x `div` wordSize)
    where
        wordSize :: Natural
        wordSize = 2 ^ value @r

toZp :: forall p a. (Arithmetic a, KnownNat p) => Vector Size a -> Zp p
toZp = fromConstant . impl
  where
    mods :: Vector Size Natural
    mods = coprimes @a

    binary :: Natural -> Natural -> Integer
    binary g m = (fromConstant g * 2 ^ sigma) `div` fromConstant m

    impl :: Vector Size a -> Natural
    impl xs =
      let gs0 = zipWith (\x y -> toConstant x * y) xs $ minv @a
          gs = zipWith mod gs0 mods
          residue = floorN ((3 % 4) + sum (zipWith binary gs mods) % (2 ^ sigma))
       in vectorDotProduct gs (mis @a @p) -! mprod @a @p * residue

fromZp :: forall p a. Arithmetic a => Zp p -> Vector Size a
fromZp = (\(FFA0 (Interpreter xs) :: FFA0 p (Interpreter a)) -> xs) . fromConstant

-- | Subtracts @m@ from @i@ if @i@ is not less than @m@
--
condSubOF :: forall i a w m . (MonadCircuit i a w m, Arithmetic a) => Natural -> i -> m (i, i)
condSubOF m i = do
  z <- newAssigned zero
  bm <- forM (wordExpansion @8 m ++ [0]) $ \x -> if x Haskell.== 0 then pure z else newAssigned (fromConstant x)
  bi <- expansionW @8 (length bm) i
  ovf <- blueprintGE @8 (Haskell.reverse bi) (Haskell.reverse bm)
  res <- newAssigned (($ i) - ($ ovf) * fromConstant m)
  return (res, ovf)

condSub :: (MonadCircuit i a w m, Arithmetic a) => Natural -> i -> m i
condSub m x = fst <$> condSubOF m x

smallCut :: forall i a w m. (Arithmetic a, MonadCircuit i a w m) => Vector Size i -> m (Vector Size i)
smallCut = zipWithM condSub $ coprimes @a

bigSub :: (Arithmetic a, MonadCircuit i a w m) => Natural -> i -> m i
bigSub m j = trimPow j >>= trimPow >>= condSub m
  where
    s = Haskell.ceiling (log2 m) :: Natural
    trimPow i = do
      (l, h) <- splitExpansion s s i
      newAssigned (($ l) + ($ h) * fromConstant ((2 ^ s) -! m))

bigCut :: forall i a w m. (Arithmetic a, MonadCircuit i a w m) => Vector Size i -> m (Vector Size i)
bigCut = zipWithM bigSub $ coprimes @a

cast :: forall p i a w m. (KnownNat p, Arithmetic a, MonadCircuit i a w m) => Vector Size i -> m (Vector Size i)
cast xs = do
  gs <- zipWithM (\i m -> newAssigned $ ($ i) * fromConstant m) xs (minv @a) >>= bigCut
  zi <- newAssigned (const zero)
  let binary g m = snd <$> iterateM sigma (binstep m) (g, zi)
      binstep m (i, ci) = do
        (i', j) <- newAssigned (($ i) + ($ i)) >>= condSubOF @i @a @w @m m
        ci' <- newAssigned (($ ci) + ($ ci) + ($ j))
        return (i', ci')
  base <- newAssigned (fromConstant (3 * (2 ^ (sigma -! 2)) :: Natural))
  let ms = coprimes @a
  residue <- zipWithM binary gs ms
        >>= foldlM (\i j -> newAssigned (($ i) + ($ j))) base
        >>= (fmap snd . splitExpansion sigma (numberOfBits @a -! sigma))
  for ms $ \m -> do
    dot <- zipWithM (\i x -> newAssigned (($ i) * fromConstant (x `mod` m))) gs (mis @a @p)
            >>= traverse (bigSub m)
            >>= foldlM (\i j -> newAssigned (($ i) + ($ j))) zi
    newAssigned (($ dot) + fromConstant (m -! (mprod @a @p `mod` m)) * ($ residue))
        >>= bigSub m

mul :: forall p i a w m. (KnownNat p, Arithmetic a, NFData i, MonadCircuit i a w m) => Vector Size i -> Vector Size i -> m (Vector Size i)
mul xs ys = Haskell.fmap force $ zipWithM (\i j -> newAssigned (\w -> w i * w j)) xs ys >>= bigCut >>= cast @p

natPowM :: Monad m => (a -> a -> m a) -> m a -> Natural -> a -> m a
natPowM _ z 0 _ = z
natPowM _ _ 1 x = pure x
natPowM f z n x
  | Haskell.even n    = natPowM f z (n `div` 2) x >>= \y -> f y y
  | Haskell.otherwise = natPowM f z (n -! 1) x >>= f x

oneM :: MonadCircuit i a w m => m (Vector Size i)
oneM = pure <$> newAssigned (const one)

instance (KnownNat p, Arithmetic a) => ToConstant (FFA0 p (Interpreter a)) where
  type Const (FFA0 p (Interpreter a)) = Zp p
  toConstant (FFA0 (Interpreter rs)) = toZp rs

instance (FromConstant a (Zp p), Symbolic c) => FromConstant a (FFA0 p c) where
  fromConstant = FFA0 . embed . impl . toConstant . (fromConstant :: a -> Zp p)
    where
      impl :: Natural -> Vector Size (BaseField c)
      impl x = fromConstant . (x `mod`) <$> coprimes @(BaseField c)

instance {-# OVERLAPPING #-} FromConstant (FFA0 p c) (FFA0 p c)

instance {-# OVERLAPPING #-} (KnownNat p, Symbolic c) => Scale (FFA0 p c) (FFA0 p c)

instance (KnownNat p, Symbolic c) => MultiplicativeSemigroup (FFA0 p c) where
  FFA0 x * FFA0 y =
    FFA0 $ symbolic2F x y (\u v -> fromZp (toZp u * toZp v :: Zp p)) (mul @p)

instance (KnownNat p, Symbolic c) => Exponent (FFA0 p c) Natural where
  FFA0 x ^ a =
    FFA0 $ symbolicF x (\v -> fromZp (toZp v ^ a :: Zp p)) $ natPowM (mul @p) oneM a

instance (KnownNat p, Symbolic c) => MultiplicativeMonoid (FFA0 p c) where
  one = fromConstant (one :: Zp p)

instance (KnownNat p, Symbolic c) => AdditiveSemigroup (FFA0 p c) where
  FFA0 x + FFA0 y =
    FFA0 $ symbolic2F x y (\u v -> fromZp (toZp u + toZp v :: Zp p)) $ \xs ys ->
      zipWithM (\i j -> newAssigned (\w -> w i + w j)) xs ys >>= smallCut >>= cast @p

instance (KnownNat p, Scale a (Zp p), Symbolic c) => Scale a (FFA0 p c) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (KnownNat p, Symbolic c) => AdditiveMonoid (FFA0 p c) where
  zero = fromConstant (zero :: Zp p)

instance (KnownNat p, Symbolic c) => AdditiveGroup (FFA0 p c) where
  negate (FFA0 x) = FFA0 $ symbolicF x (fromZp . negate . toZp @p) $ \xs -> do
    let cs = coprimes @(BaseField c)
    ys <- zipWithM (\i m -> newAssigned $ fromConstant m - ($ i)) xs cs
    cast @p ys

instance (KnownNat p, Symbolic c) => Semiring (FFA0 p c)

instance (KnownNat p, Symbolic c) => Ring (FFA0 p c)

instance (Prime p, Symbolic c) => Exponent (FFA0 p c) Integer where
  x ^ a = x `intPowF` (a `mod` fromConstant (value @p -! 1))

instance (Prime p, Symbolic c) => Field (FFA0 p c) where
  finv (FFA0 x) =
    FFA0 $ symbolicF x (fromZp . finv @(Zp p) . toZp)
      $ natPowM (mul @p) oneM (value @p -! 2)

instance Finite (Zp p) => Finite (FFA0 p b) where
  type Order (FFA0 p b) = p

-- FIXME: This Eq instance is wrong
deriving newtype instance Symbolic c => Eq (Bool c) (FFA0 p c)

deriving newtype instance Symbolic c => Conditional (Bool c) (FFA0 p c)

-- | TODO: fix when rewrite is done
instance (Symbolic c) => SymbolicInput (FFA0 p c) where
  isValid _ = true


---------------------------------- Some staff ----------------------------------
{-
newtype FieldElement c = FieldElement { fromFieldElement :: c Par1 }

k -> BaseField c -> Par1 (BaseField c) -> c Par1 -> FieldElement c

data Point (curve :: Type) = Point
  { _x     :: BaseField curve
  , _y     :: BaseField curve
  , _isInf :: BooleanOf curve
  } deriving (Generic)

type Fr = Zp BLS12_381_Scalar
type Fq = Zp BLS12_381_Base

instance EllipticCurve BLS12_381_G1 where
    type ScalarField BLS12_381_G1 = Fr

    type BaseField BLS12_381_G1 = Fq

newtype Zp (p :: Natural) = Zp Integer
    deriving (Generic, NFData)

{-# INLINE fromZp #-}
fromZp :: Zp p -> Natural
fromZp (Zp a) = fromIntegral a

{-# INLINE residue #-}
residue :: forall p . KnownNat p => Integer -> Integer
residue = (`Haskell.mod` fromIntegral (value @p))

{-# INLINE toZp #-}
toZp :: forall p . KnownNat p => Integer -> Zp p
toZp = Zp . residue @p

Natural -> Vector Size (BaseField c) -> c (Vector Size) -> FFA0 p c

Par1 Fr ~ i (ScalarField c1)

PlonkupRelation p i n l (ScalarField c1)

-}
{-
Residue Numeral System
Representation of an integer holding its values modulo several coprime integers.

Contains all the necessary values to carry out operations such as
multiplication and reduction in this representation.

Representation of an integer.

The integer is represented as a vector of [`Limb`]s with values in the
native field plus a reference to the [`FFALimb`] used.
-}
--------------------------------- General FFA0 ----------------------------------

type LimbsMaxSize = 256
type LimbMaxBits = 68


{-
a * b = r mod p

a_n -> nlimbs
bits_length(r) ~ bits

`t = BIT_LEN_LIMB * NUMBER_OF_LIMBS`
`T = 2 ^ t` which we also name as `binary_modulus`
-}

{-
  -- Actual limbs FFA0 representation.
  { limbs :: c (Vector nlimbs)
-}

data FFA (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) = FFA {limbs :: (Vector nlimbs (Zp n)), ffalimb :: FFALimb w n nlimbs bits}

-- TODO: refactor the code to be able to use two different curves (native and non-native)
data FFALimb (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) = FFALimb
  -- Order of the wrong field W. (In the article `p`).
  { wrong_modulus  :: Natural
  -- Order of the native field N. (In the article `n`).
  , native_modulus :: Natural
  -- In the article: 2^t
  , binary_modulus :: Natural
  -- In the article notation: M = n * 2^t
  , crt_modulus    :: Natural

  -- Native field elements representing `2^(i*-r)` with `bits_length(r) = bits`.
  , right_shifters :: Vector nlimbs (Zp n)
  -- Native field elements representing `2^(i*r)` with `bits_length(r) = bits`.
  , left_shifters  :: Vector nlimbs (Zp n)
  -- The value `base_aux` is a vector of auxiliary limbs representing the value `2p` with `p` the size of the wrong modulus.
  , base_aux       :: Vector nlimbs Natural

  -- Negative wrong modulus: `-p mod 2^t` as vector of limbs.
  , negative_wrong_modulus_decomposed :: Vector nlimbs (Zp n)
  -- Wrong modulus `p` as vector of limbs.
  , wrong_modulus_decomposed          :: Vector nlimbs (Zp n)
  -- Wrong modulus -1  `p - 1` as vector of limbs.
  , wrong_modulus_minus_one           :: Vector nlimbs (Zp n)
  -- Wrong modulus as native field element: `p mod n`.
  , wrong_modulus_in_native_modulus   :: Zp n

  -- Maximum value for a reduced limb.
  , max_reduced_limb   :: Natural
  -- Maximum value for an unreduced limb.
  , max_unreduced_limb :: Natural
  -- Maximum value of the remainder.
  , max_remainder      :: Natural
  -- Maximum value that can be safely multiplied (guaranteeing the result will be reducible).
  , max_operand        :: Natural
  -- Maximum value of the quotient `q` in a reduction.
  , max_mul_quotient   :: Natural

  -- Maximum value of most significant limb for `max_reduced_limb`.
  , max_most_significant_reduced_limb      :: Natural
  -- Maximum value of most significant limb for `max_operand_limb`.
  , max_most_significant_operand_limb      :: Natural
  -- Maximum value of most significant limb for `max_mul_quotient`.
  , max_most_significant_mul_quotient_limb :: Natural

  -- Bit length of the maximum value allowed for residues in multiplication.
  -- TODO: implement , mul_v_bit_len :: Natural
  -- Bit length of the maximum value allowed for residues in reduction circuit.
  -- TODO: implement , red_v_bit_len :: Natural
  }

{-

-}

bitLenExpansion :: forall nlimbs bits. (KnownNat nlimbs, KnownNat bits) => Natural -> [Natural]
bitLenExpansion e = expansion e nlimbs
  where
    nlimbs  = P.fromIntegral $ value @nlimbs
    bit_len = P.fromIntegral $ value @bits
    mask :: Natural = 1 `shiftL` bit_len

    expansion :: Natural -> Int -> [Natural]
    expansion 0 0 = []
    expansion n i = (n .&. mask) : expansion (n `shiftR` bit_len) (i P.- 1)

decomposeBig :: forall nlimbs bits f. (KnownNat nlimbs, KnownNat bits, KnownNat f) =>
  Natural -> Vector nlimbs (Zp f)
decomposeBig = unsafeToVector . fmap (PrimeField.toZp . fromConstant) . bitLenExpansion @nlimbs @bits

calculateBaseAux :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime w, Prime n) => Vector nlimbs Natural
calculateBaseAux = base_aux
  where
      two = PrimeField.toZp @n 2
      r   = PrimeField.fromZp $ two ^ (value @bits)
      w :: Natural = value @w
      wrong_modulus = decomposeBig @nlimbs @bits @n w
      -- `base_aux = 2 * wrong_modulus`
      base_aux' = fmap PrimeField.fromZp wrong_modulus
      aux = fromVector $ reverse base_aux'
      last = P.head aux
      base_aux = unsafeToVector $ P.reverse $ borrowNext last (P.tail aux)

      bits = P.fromIntegral $ value @bits

      -- If value of a limb is not above dense limb borrow from the next one
      borrowNext :: Natural -> [Natural] -> [Natural]
      borrowNext l [] = [l]
      borrowNext l (l' : ls) = if countBits l' P.< bits P.+ 1 then
        let new_l = l -! 1; new_l' = l' + r in new_l : borrowNext new_l' ls
        else l : borrowNext l' ls

countBits :: Natural -> Int
countBits = undefined

constructFFALimb :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime w, Prime n) => FFALimb w n nlimbs bits
constructFFALimb = do
  let nlimbs  :: Natural = value @nlimbs
      bit_len :: Natural = value @bits

      -- `t = BIT_LEN_LIMB * NUMBER_OF_LIMBS`
      -- `T = 2 ^ t` which we also name as `binary_modulus`
      binary_modulus_bit_len = P.fromIntegral $ bit_len * nlimbs
      binary_modulus = one `shiftL` binary_modulus_bit_len

      -- wrong field modulus: `w`
      wrong_modulus :: Natural = value @w
      -- native field modulus: `n`
      native_modulus :: Natural = value @n
      -- Multiplication is constrained as:
      --
      -- `a * b = w * quotient + remainder`
      --
      -- where `quotient` and `remainder` is witnesses, `a` and `b` are assigned
      -- operands. Both sides of the equation must not wrap `crt_modulus`.
      crt_modulus = binary_modulus * native_modulus

      -- Witness remainder might overflow the wrong modulus but it is limited
      -- to the next power of two of the wrong modulus.
      max_remainder = (one `shiftL` P.fromIntegral wrong_modulus) -! one

      -- Find maxium quotient that won't wrap `quotient * wrong + remainder` side of
      -- the equation under `crt_modulus`.
      pre_max_quotient = (crt_modulus -! max_remainder) `div` wrong_modulus

      -- Lower this value to make this value suitable for bit range checks.
      max_quotient = (one `shiftL` P.fromIntegral (pre_max_quotient -! one)) -! one

      -- Find the maximum operand: in order to meet completeness maximum allowed
      -- operand value is saturated as below:
      --
      -- `max_operand ^ 2 < max_quotient * wrong + max_remainder`
      --
      -- So that prover can find `quotient` and `remainder` witnesses for any
      -- allowed input operands. And it also automativally ensures that:
      --
      -- `max_operand^2 < crt_modulus`
      --
      -- must hold.
      max_operand_bit_len = (countBits (max_quotient * wrong_modulus + max_remainder) P.- 1) `P.div` 2;
      max_operand = (one `shiftL` max_operand_bit_len) -! one

      -- negative wrong field modulus moduli binary modulus `w'`
      -- `w' = (T - w)`
      -- `w' = [w'_0, w'_1, ... ]`
      negative_wrong_modulus_decomposed = decomposeBig @nlimbs @bits @n $ binary_modulus -! wrong_modulus

      --`w = [w_0, w_1, ... ]`
      wrong_modulus_decomposed = decomposeBig @nlimbs @bits @n wrong_modulus

      --`w-1 = [w_0-1 , w_1, ... ] `
      wrong_modulus_minus_one = decomposeBig @nlimbs @bits @n $ wrong_modulus -! one

      -- Full dense limb without overflow
      max_reduced_limb = (one `shiftL` P.fromIntegral bit_len) -! one

      -- Keep this much lower than what we can reduce with single limb quotient to
      -- take extra measure for overflow issues
      max_unreduced_limb = (one `shiftL` P.fromIntegral (bit_len + bit_len `P.div` 2)) -! one

      -- Most significant limbs are subjected to different range checks which will be
      -- probably less than full sized limbs.
      max_most_significant_reduced_limb = max_remainder `shiftR` P.fromIntegral ((nlimbs -! 1) * bit_len)
      max_most_significant_operand_limb = max_operand `shiftR` P.fromIntegral ((nlimbs -! 1) * bit_len)
      max_most_significant_mul_quotient_limb = max_quotient `shiftR` P.fromIntegral ((nlimbs -! 1) * bit_len)

      -- Emulate a multiplication to find out max residue overflows:
      -- let mut mul_v_bit_len: usize = BIT_LEN_LIMB
      -- TODO: implement mul_v_bit_len = bit_len

      -- Emulate a multiplication to find out max residue overflows:
      -- let mut red_v_bit_len: usize = BIT_LEN_LIMB;
      -- TODO: implement red_v_bit_len = bit_len

      -- let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;

      -- Calculate auxillary value for subtraction
      base_aux = calculateBaseAux @nlimbs @bits @w @n

      wrong_modulus_in_native_modulus :: Zp n = PrimeField.toZp $ fromConstant $ wrong_modulus `P.mod` native_modulus

      -- Calculate shifter elements
      two     = PrimeField.toZp @n 2 
      two_inv = finv two

      -- Right shifts field element by `u * BIT_LEN_LIMB` bits
      right_shifters = unsafeToVector $ fmap (\i -> two_inv ^ (i * bit_len)) [0..nlimbs]

      -- Left shifts field element by `u * BIT_LEN_LIMB` bits
      left_shifters = unsafeToVector $ fmap (\i -> two ^ (i * bit_len)) [0..nlimbs]

      max_mul_quotient = max_quotient

  FFALimb{..}

-- toZp / fromZp, ToConstant (type Zp a) / FromConstant a

-- (+), (-), (*), (negate), (^), (finv)

-- cast, isValid



------------------------------------ Setup -------------------------------------

-- a, b \in [0, p)

-- a * b = r mod p, r \in [0, p)

-- a * b = q * p + r, a * b < p^2

-- a * b - r = q * p < p^2, q \in [0, p)

-- circumventing the computation of a * b or q * p

-- (a, b, q, p, r)

--------------------------- Native Field Constraint ----------------------------

-- a * b = r mod p => a * b = q * p + r

-- a * b - q * p - r = 0 mod n, prim n < p
-- min_n

-- v_a * n + a_n = a
-- v_b * n + b_n = b
-- v_q * n + q_n = q
-- v_p * n + p_n = p
-- v_r * n + r_n = r

-- v_overall * n = a_n * b_n - q_n * p_n - r_n

-- (a, b, q, p, r, v_a, v_b, v_q, v_p, v_r, v_overall)

---------- Constraint decomposition in modulo 2^𝑇 ring, where 𝑝 < 2^𝑇 ----------

-- T \in [4, 254]

-- p' = -p mod 2^T => p' = 2^T - p

-- a * b - q * p = a * b + q * p' mod 2^T

-- B = T/4

-- ...

--------------------------------------------------------------------------------



