{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE DerivingStrategies       #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances     #-}

module ZkFold.Symbolic.Data.FFA where
  -- (FFAOld (..), Size, coprimesDownFrom, coprimes)

import           Control.Applicative              (pure)
import           Control.DeepSeq                  (NFData, force)
import           Control.Monad                    (Monad, forM, return, (>>=))
import           Control.Monad.State
import           Data.Bits                        (Bits (..))
import           Data.Foldable                    (any, foldlM, for_)
import qualified Data.Foldable                    as F
import           Data.Function                    (const, ($), (.))
import           Data.Functor                     (fmap, (<$>))
import           Data.List                        (dropWhile, mapAccumL, (++))
import           Data.Ratio                       ((%))
import           Data.Semialign
import           Data.Traversable                 (for, traverse)
import           Data.Tuple                       (fst, snd, uncurry)
import qualified Data.Vector                      as V
import qualified Data.Vector.Mutable              as Mutable
import           Data.Zip                         (zipWith)
import           Prelude                          (Int, Integer, error, undefined)
import qualified Prelude                          as Haskell
import qualified Prelude                          as P

import           ZkFold.Base.Algebra.Basic.Class  hiding (invert)
import qualified ZkFold.Base.Algebra.Basic.Field  as PrimeField
import           ZkFold.Base.Algebra.Basic.Field  (Zp, inv)
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

type Size = 7

-- | Foreign-field arithmetic based on https://cr.yp.to/papers/mmecrt.pdf
newtype FFAOld (p :: Natural) c = FFAOld (c (Vector Size))

deriving newtype instance Symbolic c => SymbolicData (FFAOld p c)
deriving newtype instance NFData (c (Vector Size)) => NFData (FFAOld p c)
deriving newtype instance Haskell.Show (c (Vector Size)) => Haskell.Show (FFAOld p c)

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
fromZp = (\(FFAOld (Interpreter xs) :: FFAOld p (Interpreter a)) -> xs) . fromConstant

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

mul0 :: forall p i a w m. (KnownNat p, Arithmetic a, NFData i, MonadCircuit i a w m) => Vector Size i -> Vector Size i -> m (Vector Size i)
mul0 xs ys = Haskell.fmap force $ zipWithM (\i j -> newAssigned (\w -> w i * w j)) xs ys >>= bigCut >>= cast @p

natPowM :: Monad m => (a -> a -> m a) -> m a -> Natural -> a -> m a
natPowM _ z 0 _ = z
natPowM _ _ 1 x = pure x
natPowM f z n x
  | Haskell.even n    = natPowM f z (n `div` 2) x >>= \y -> f y y
  | Haskell.otherwise = natPowM f z (n -! 1) x >>= f x

oneM :: MonadCircuit i a w m => m (Vector Size i)
oneM = pure <$> newAssigned (const one)

instance (KnownNat p, Arithmetic a) => ToConstant (FFAOld p (Interpreter a)) where
  type Const (FFAOld p (Interpreter a)) = Zp p
  toConstant (FFAOld (Interpreter rs)) = toZp rs

instance (FromConstant a (Zp p), Symbolic c) => FromConstant a (FFAOld p c) where
  fromConstant = FFAOld . embed . impl . toConstant . (fromConstant :: a -> Zp p)
    where
      impl :: Natural -> Vector Size (BaseField c)
      impl x = fromConstant . (x `mod`) <$> coprimes @(BaseField c)

instance {-# OVERLAPPING #-} FromConstant (FFAOld p c) (FFAOld p c)

instance {-# OVERLAPPING #-} (KnownNat p, Symbolic c) => Scale (FFAOld p c) (FFAOld p c)

instance (KnownNat p, Symbolic c) => MultiplicativeSemigroup (FFAOld p c) where
  FFAOld x * FFAOld y =
    FFAOld $ symbolic2F x y (\u v -> fromZp (toZp u * toZp v :: Zp p)) (mul0 @p)

instance (KnownNat p, Symbolic c) => Exponent (FFAOld p c) Natural where
  FFAOld x ^ a =
    FFAOld $ symbolicF x (\v -> fromZp (toZp v ^ a :: Zp p)) $ natPowM (mul0 @p) oneM a

instance (KnownNat p, Symbolic c) => MultiplicativeMonoid (FFAOld p c) where
  one = fromConstant (one :: Zp p)

instance (KnownNat p, Symbolic c) => AdditiveSemigroup (FFAOld p c) where
  FFAOld x + FFAOld y =
    FFAOld $ symbolic2F x y (\u v -> fromZp (toZp u + toZp v :: Zp p)) $ \xs ys ->
      zipWithM (\i j -> newAssigned (\w -> w i + w j)) xs ys >>= smallCut >>= cast @p

instance (KnownNat p, Scale a (Zp p), Symbolic c) => Scale a (FFAOld p c) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (KnownNat p, Symbolic c) => AdditiveMonoid (FFAOld p c) where
  zero = fromConstant (zero :: Zp p)

instance (KnownNat p, Symbolic c) => AdditiveGroup (FFAOld p c) where
  negate (FFAOld x) = FFAOld $ symbolicF x (fromZp . negate . toZp @p) $ \xs -> do
    let cs = coprimes @(BaseField c)
    ys <- zipWithM (\i m -> newAssigned $ fromConstant m - ($ i)) xs cs
    cast @p ys

instance (KnownNat p, Symbolic c) => Semiring (FFAOld p c)

instance (KnownNat p, Symbolic c) => Ring (FFAOld p c)

instance (Prime p, Symbolic c) => Exponent (FFAOld p c) Integer where
  x ^ a = x `intPowF` (a `mod` fromConstant (value @p -! 1))

instance (Prime p, Symbolic c) => Field (FFAOld p c) where
  finv (FFAOld x) =
    FFAOld $ symbolicF x (fromZp . finv @(Zp p) . toZp)
      $ natPowM (mul0 @p) oneM (value @p -! 2)

instance Finite (Zp p) => Finite (FFAOld p b) where
  type Order (FFAOld p b) = p

-- FIXME: This Eq instance is wrong
deriving newtype instance Symbolic c => Eq (Bool c) (FFAOld p c)

deriving newtype instance Symbolic c => Conditional (Bool c) (FFAOld p c)

-- | TODO: fix when rewrite is done
instance (Symbolic c) => SymbolicInput (FFAOld p c) where
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

Natural -> Vector Size (BaseField c) -> c (Vector Size) -> FFAOld p c

Par1 Fr ~ i (ScalarField c1)

PlonkupRelation p i n l (ScalarField c1)

-}
--------------------------------- General FFALimbs ----------------------------------

type LimbsMaxSize = 256
type LimbMaxBits = 68

-- Reduction witness contains all values that needs to be assigned in
-- multiplication gate.
data ReductionWitness (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) = ReductionWitness
    { result       :: FFA w n nlimbs bits
    , quotient     :: Quotient w n nlimbs bits
    , intermediate :: Vector nlimbs (Zp n)
    , residuesW    :: V.Vector (Zp n)
    }

-- Quotient term in [`ReductionWitness`].
--
-- There are two possible representations:
-- Short: as an element of the native field.
-- Long : as an [`FFA`].
data Quotient (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) =
      Short (Zp n)
    | Long (FFA w n nlimbs bits)

data FFA (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) = FFA {limbs :: Vector nlimbs (Zp n), ffalimb :: FFALimb w n nlimbs bits}

-- TODO: refactor the code to be able to use two different curves (native and non-native)
data FFALimb (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) = FFALimb
  -- Order of the wrong field W. (In the article `p`).
  { wrong_modulus                          :: Natural
  -- Order of the native field N. (In the article `n`).
  , native_modulus                         :: Natural
  -- In the article: 2^t
  , binary_modulus                         :: Natural
  -- In the article notation: M = n * 2^t
  , crt_modulus                            :: Natural

  -- Native field elements representing `2^(i*-r)` with `bits_length(r) = bits`.
  , right_shifters                         :: Vector nlimbs (Zp n)
  -- Native field elements representing `2^(i*r)` with `bits_length(r) = bits`.
  , left_shifters                          :: Vector nlimbs (Zp n)
  -- The value `base_aux` is a vector of auxiliary limbs representing the value `2p` with `p` the size of the wrong modulus.
  , base_aux                               :: Vector nlimbs Natural

  -- Negative wrong modulus: `-p mod 2^t` as vector of limbs.
  , negative_wrong_modulus_decomposed      :: Vector nlimbs (Zp n)
  -- Wrong modulus `p` as vector of limbs.
  , wrong_modulus_decomposed               :: Vector nlimbs (Zp n)
  -- Wrong modulus -1  `p - 1` as vector of limbs.
  , wrong_modulus_minus_one                :: Vector nlimbs (Zp n)
  -- Wrong modulus as native field element: `p mod n`.
  , wrong_modulus_in_native_modulus        :: Zp n

  -- Maximum value for a reduced limb.
  , max_reduced_limb                       :: Natural
  -- Maximum value for an unreduced limb.
  , max_unreduced_limb                     :: Natural
  -- Maximum value of the remainder.
  , max_remainder                          :: Natural
  -- Maximum value that can be safely multiplied (guaranteeing the result will be reducible).
  , max_operand                            :: Natural
  -- Maximum value of the quotient `q` in a reduction.
  , max_mul_quotient                       :: Natural

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

      wrong_modulus_in_native_modulus :: Zp n = PrimeField.toZp $ fromConstant $ wrong_modulus `mod` native_modulus

      -- Calculate shifter elements
      two     = PrimeField.toZp @n 2
      two_inv = finv two

      -- Right shifts field element by `u * BIT_LEN_LIMB` bits
      right_shifters = unsafeToVector $ fmap (\i -> two_inv ^ (i * bit_len)) [0..nlimbs]

      -- Left shifts field element by `u * BIT_LEN_LIMB` bits
      left_shifters = unsafeToVector $ fmap (\i -> two ^ (i * bit_len)) [0..nlimbs]

      max_mul_quotient = max_quotient

  FFALimb{..}

fromWrong :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime n) => Zp w -> FFALimb w n nlimbs bits -> FFA w n nlimbs bits
fromWrong w = fromBig (toConstant w)

fromBig :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime n) => Natural -> FFALimb w n nlimbs bits -> FFA w n nlimbs bits
fromBig e = FFA (decomposeBig @nlimbs @bits @n e)

-- Compute the represented value by a vector of values and a bit length.
--
-- This function is used to compute the value of an integer
-- passing as input its limb values and the bit length used.
-- Returns the sum of all limbs scaled by 2^(bit_len * i)
compose :: forall nlimbs bits . KnownNat bits => Vector nlimbs Natural -> Natural
compose limbs = F.foldl (\acc val -> (acc `shiftL` bit_len) + val) 0 (reverse limbs)
  where
    bit_len = P.fromIntegral $ value @bits

-- Computes the inverse of the [`Integer`] as an element of the Wrong
-- field. Returns `None` if the value cannot be inverted.
invert :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime w, Prime n) => FFA w n nlimbs bits -> FFA w n nlimbs bits
invert (FFA limbs ffalimb) = fromWrong @nlimbs @bits @w w ffalimb
  where w = finv . PrimeField.toZp @w . fromConstant . compose @nlimbs @bits $ fmap toConstant limbs

-- Computes the witness values for squaring operation
square :: (KnownNat nlimbs, KnownNat bits, Prime n) => FFA w n nlimbs bits -> ReductionWitness w n nlimbs bits
square a = mul a a

-- Computes the witness values for multiplication operation
mul :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime n) => FFA w n nlimbs bits -> FFA w n nlimbs bits -> ReductionWitness w n nlimbs bits
mul s@(FFA limbs ffalimb) (FFA otherLimbs _) = ReductionWitness result (Long quotient) t residuesW
  where
    negative_modulus     = negative_wrong_modulus_decomposed ffalimb
    self                 = compose @nlimbs @bits $ fmap toConstant limbs
    other                = compose @nlimbs @bits $ fmap toConstant otherLimbs
    (quotient', result') = (self * other) `divMod` wrong_modulus ffalimb
    quotient             = fromBig quotient' ffalimb
    result               = fromBig result' ffalimb
    t                    = unsafeToVector $ repeat 0
    {-
    for k in 0..NUMBER_OF_LIMBS {
        for i in 0..=k {
            let j = k - i;
            t[i + j] = t[i + j]
                + self.limb(i).0 * other.limb(j).0
                + negative_modulus[i] * quotient.limb(j).0;
        }
    }
    -}
    residuesW = residues s t

-- Returns division witnesses
div' :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime w, Prime n) => FFA w n nlimbs bits -> FFA w n nlimbs bits -> ReductionWitness w n nlimbs bits
div' s@(FFA limbs' ffalimb) o@(FFA otherLimbs _) = ReductionWitness result (Long quotient) intermediate residuesW
  where
    modulus              = wrong_modulus ffalimb
    self                 = compose @nlimbs @bits $ fmap toConstant limbs'
    other_invert         = compose @nlimbs @bits $ fmap toConstant $ limbs $ invert o
    result'              = (self * other_invert) `mod` modulus
    other                = compose @nlimbs @bits $ fmap toConstant otherLimbs
    negative_modulus     = negative_wrong_modulus_decomposed ffalimb
    (quotient', reduced) = (other * result') `divMod` modulus
    -- TODO: unsafe zero div
    (k0, _must_be_zero)   = (self -! reduced) `divMod` modulus
    quotient             = fromBig (quotient' -! k0) ffalimb
    result               = fromBig result' ffalimb
    intermediate         = Vector $ snd $ runState step (V.replicate (P.fromIntegral $ value @nlimbs) 0)
    -- create :: (forall s. ST s (MVector s a)) -> Vector a

    step :: State (V.Vector (Zp n)) ()
    step = undefined {- do
      for_ [0 .. value @nlimbs] $ \k -> do
        for_ [0 .. k] $ \i -> do
          let j = k -! i
          vec <- get
          let a = vec V.! P.fromIntegral (i + j)
          Mutable.write vec (P.fromIntegral $ i + j) a -}
    {-
        for k in 0..NUMBER_OF_LIMBS {
            for i in 0..=k {
                let j = k - i;
                intermediate[i + j] = intermediate[i + j]
                    + result.limb(i).0 * other.limb(j).0
                    + negative_modulus[i] * quotient.limb(j).0;
            }
        }
    -}
    residuesW = residues s intermediate

-- Computes the witness values for reduction operation
reduce :: forall nlimbs bits w n. (KnownNat nlimbs, KnownNat bits, Prime n) => FFA w n nlimbs bits -> ReductionWitness w n nlimbs bits
reduce (FFA limbs ffalimb) = ReductionWitness result (Short quotient) t residuesW
  where
    modulus              = wrong_modulus ffalimb
    negative_modulus     = negative_wrong_modulus_decomposed ffalimb
    self                 = compose @nlimbs @bits $ fmap toConstant limbs
    (quotient', result') = self `divMod` modulus
    quotient             = PrimeField.toZp @n . fromConstant $ quotient'
    t                    = (\(a, p) -> a + p * quotient) <$> zip limbs negative_modulus
    result               = fromBig result' ffalimb
    residuesW            = residues result t

residues :: forall nlimbs bits w n. (KnownNat nlimbs, Prime n) => FFA w n nlimbs bits -> Vector nlimbs (Zp n) -> V.Vector (Zp n)
residues (FFA limbs ffalimb) t = snd $ mapAccumL step zero (V.fromList $ repeat 0)
  where
    nlimbs       = value @nlimbs
    u_len        = (nlimbs + 1) `div` 2
    lsh1         = left_shifters ffalimb !! 1
    (rsh1, rsh2) = (right_shifters ffalimb !! 1, right_shifters ffalimb !! 2)
    -- TODO: use chunks
    step :: Zp n -> Natural -> (Zp n, Zp n)
    step carry i = (v, v)
      where
        j = 2 * i
        v = if (i == u_len -! 1) && P.odd nlimbs
            then (t !! j - limbs !! j) * rsh1
            else let (r_0, r_1) = (limbs !! j, limbs !! (j + 1))
                     (t_0, t_1) = (t !! j, t !! j + 1)
                     u = t_0 + (t_1 * lsh1) - r_0 - (lsh1 * r_1) + carry
                  in u * rsh2


-- AssignedLimb is a limb of an non native integer
data AssignedLimb (n :: Natural) = AssignedLimb
    { -- witnessValue :: Witness value
      witnessValue :: Zp n
      -- max_val :: Maximum value to track overflow and reduction flow
    , max_val      :: Natural
    }

data AssignedFFA (w :: Natural) (n :: Natural) (nlimbs :: Natural) (bits :: Natural) = AssignedFFA
    { -- Limbs of the emulated integer
      assignedLimbs   :: Vector nlimbs (AssignedLimb n)
      -- Value in the scalar field
    , assignedNative  :: Zp n
      -- Share ffalimb across all `AssignedFFA`s
    , assignedFfalimb :: FFALimb w n nlimbs bits
    }

-- toZp / fromZp, ToConstant (type Zp a) / FromConstant a

-- (+), (-), (*), (negate), (^), (finv)

-- cast, isValid
