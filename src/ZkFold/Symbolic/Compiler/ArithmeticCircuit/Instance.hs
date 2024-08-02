{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Control.Monad                                             (foldM, replicateM)
import           Data.Aeson                                                hiding (Bool)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map,
                                                                            null, splitAt, take)
import           Data.Traversable                                          (Traversable, for)
import qualified Data.Zip                                                  as Z
import           GHC.Generics                                              (Par1 (..))
import           GHC.Num                                                   (integerToNatural)
import           Prelude                                                   (Integer, Show, const, mempty, pure, return,
                                                                            show, type (~), ($), (++), (.), (<$>),
                                                                            (>>=))
import qualified Prelude                                                   as Haskell
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (arbitrary), Gen, chooseInteger,
                                                                            elements)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.HFunctor                                 (HFunctor, hmap)
import           ZkFold.Base.Data.Par1                                     ()
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embed, embedAll, embedV, expansion,
                                                                            foldCircuit, getAllVars, horner, invertC,
                                                                            isZeroC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit, circuitF)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class                                (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.DiscreteField
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.MonadCircuit                              (newAssigned)

------------------------------------- Instances -------------------------------------

instance HFunctor c => SymbolicData c (c Par1) where
    type Support c (c Par1) = ()
    type TypeSize c (c Par1) = 1

    pieces = const . hmap (V.singleton . unPar1)
    restore = hmap (Par1 . V.item) . ($ ())

deriving newtype instance HFunctor c => SymbolicData c (Bool c)

-- TODO: I had to add these constraints and I don't like them
instance
    ( KnownNat (n * Order a)
    , KnownNat (Log2 (n * Order a - 1) + 1)
    ) => Finite (ArithmeticCircuit a (Vector n)) where
    type Order (ArithmeticCircuit a (Vector n)) = n * Order a

instance (Arithmetic a, Z.Zip f, Traversable f) => AdditiveSemigroup (ArithmeticCircuit a f) where
    r1 + r2 = circuitF $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i + x j)

instance (Arithmetic a, Scale c a, Traversable f) => Scale c (ArithmeticCircuit a f) where
    scale c r = circuitF $ do
        is <- runCircuit r
        for is $ \i -> newAssigned (\x -> (c `scale` one :: a) `scale` x i)

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (ArithmeticCircuit a (Vector n)) where
    zero = circuitF $ Vector <$> replicateM (Haskell.fromIntegral $ value @n) (newAssigned (const zero))

instance Arithmetic a => AdditiveMonoid (ArithmeticCircuit a Par1) where
    zero = embed zero

instance (Arithmetic a, Z.Zip f, Traversable f, AdditiveMonoid (ArithmeticCircuit a f)) => AdditiveGroup (ArithmeticCircuit a f) where
    negate r = circuitF $ do
        is <- runCircuit r
        for is $ \i -> newAssigned (\x -> negate (x i))

    r1 - r2 = circuitF $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i - x j)

instance (Arithmetic a, Z.Zip f, Traversable f) => MultiplicativeSemigroup (ArithmeticCircuit a f) where
    r1 * r2 = circuitF $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i * x j)

instance MultiplicativeMonoid (ArithmeticCircuit a f) => Exponent (ArithmeticCircuit a f) Natural where
    (^) = natPow

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (ArithmeticCircuit a (Vector n)) where
    one = embedV (pure one)

instance Arithmetic a => MultiplicativeMonoid (ArithmeticCircuit a Par1) where
    one = embed one

-- TODO: The constant will be replicated in all outputs. Is this the desired behaviour?
instance (Arithmetic a, FromConstant b a, KnownNat n) => FromConstant b (ArithmeticCircuit a (Vector n)) where
    fromConstant c = embedAll (fromConstant c)

instance (Arithmetic a, FromConstant b a) => FromConstant b (ArithmeticCircuit a Par1) where
    fromConstant c = embed (fromConstant c)

instance (Arithmetic a, KnownNat n) => Semiring (ArithmeticCircuit a (Vector n))

instance Arithmetic a => Semiring (ArithmeticCircuit a Par1)

instance (Arithmetic a, KnownNat n) => Ring (ArithmeticCircuit a (Vector n))

instance Arithmetic a => Ring (ArithmeticCircuit a Par1)

instance (Arithmetic a, Field (ArithmeticCircuit a f)) => Exponent (ArithmeticCircuit a f) Integer where
    (^) = intPowF

instance (Arithmetic a, KnownNat n) => Field (ArithmeticCircuit a (Vector n)) where
    finv = invertC
    rootOfUnity n = embedAll <$> rootOfUnity n

instance Arithmetic a => Field (ArithmeticCircuit a Par1) where
    finv = invertC
    rootOfUnity n = embed <$> rootOfUnity n

-- TODO: The only implementation that seems to make sense is when there is only one output.
-- It is true?
--
-- Anyway, @binaryExpansion@ of an arithmetic circuit will return copies of the same circuit with different outputs.
-- The whole point of this refactor was to avoid this.
--
-- Ideally, we want to return another ArithmeticCircuit with a number of outputs corresponding to the number of bits.
-- This does not align well with the type of @binaryExpansion@
instance Arithmetic a => BinaryExpansion (ArithmeticCircuit a Par1) where
    type Bits (ArithmeticCircuit a Par1) = ArithmeticCircuit a (Vector (NumberOfBits a))
    binaryExpansion r = circuitF $ do
        output <- runCircuit r
        bits   <- expansion (numberOfBits @a) . unPar1 $ output
        pure $ V.unsafeToVector bits
    fromBinary bits = circuit $ runCircuit bits >>= horner . V.fromVector

instance (Arithmetic a, Z.Zip f, Traversable f, Field (ArithmeticCircuit a f)) => DiscreteField' (ArithmeticCircuit a f) where
    equal r1 r2 = isZeroC (r1 - r2)

instance Arithmetic a => TrichotomyField (ArithmeticCircuit a Par1) where
    trichotomy r1 r2 =
        let
            bits1 = binaryExpansion r1
            bits2 = binaryExpansion r2
            -- zip pairs of bits in {0,1} to orderings in {-1,0,1}
            comparedBits = bits1 - bits2
            -- least significant bit first,
            -- reverse lexicographical ordering
            reverseLexicographical x y = newAssigned $ \p -> p y * p y * (p y - p x) + p x
        in
            foldCircuit reverseLexicographical comparedBits

instance (Arithmetic a, KnownNat n, 1 <= n) => DiscreteField (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a (Vector n)) where
    isZero x = Bool $ circuit $ do
        bools <- runCircuit $ isZeroC x
        foldM (\i j -> newAssigned (\p -> p i * p j)) (V.head bools) (V.tail bools)

instance Arithmetic a => DiscreteField (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a Par1) where
    isZero = Bool . isZeroC

instance (Arithmetic a, DiscreteField (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a f)) => Eq (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a f) where
    x == y = isZero (x - y)
    x /= y = not $ isZero (x - y)

instance
    ( Arithmetic a
    , SymbolicData (ArithmeticCircuit a) x
    , n ~ TypeSize (ArithmeticCircuit a) x
    , KnownNat n
    ) => Conditional (Bool (ArithmeticCircuit a)) x where

    bool brFalse brTrue (Bool b) = restore ac
        where
            f' = pieces brFalse
            t' = pieces brTrue
            ac i = circuitF (solve i)

            solve :: forall i m . MonadBlueprint i a m => Support (ArithmeticCircuit a) x -> m (Vector n i)
            solve i = do
                ts <- runCircuit (t' i)
                fs <- runCircuit (f' i)
                bs <- unPar1 <$> runCircuit b
                V.zipWithM (\x y -> newAssigned $ \p -> p bs * (p x - p y) + p y) ts fs

instance (Arithmetic a, Arbitrary a) => Arbitrary (ArithmeticCircuit a Par1) where
    arbitrary = do
        k <- integerToNatural <$> chooseInteger (2, 10)
        let ac = mempty { acInput = [1..k], acOutput = pure k }
        arbitrary' ac 10

arbitrary' :: forall a . (Arithmetic a, Arbitrary a, FromConstant a a) => ArithmeticCircuit a Par1 -> Natural -> Gen (ArithmeticCircuit a Par1)
arbitrary' ac 0 = return ac
arbitrary' ac iter = do
    let vars = getAllVars ac
    li <- elements vars
    ri <- elements vars
    let (l, r) =( ac { acOutput = pure li }, ac { acOutput = pure ri })
    ac' <- elements [
        l + r
        , l * r
        , l - r
        , l // r
        ]
    arbitrary' ac' (iter -! 1)

-- TODO: make it more readable
instance (FiniteField a, Haskell.Eq a, Show a, Show (f Natural)) => Show (ArithmeticCircuit a f) where
    show r = "ArithmeticCircuit { acInput = " ++ show (acInput r)
        ++ "\n, acSystem = " ++ show (acSystem r) ++ "\n, acOutput = " ++ show (acOutput r) ++ "\n, acVarOrder = " ++ show (acVarOrder r) ++ " }"

-- TODO: add witness generation info to the JSON object
instance (ToJSON a, ToJSON (f Natural)) => ToJSON (ArithmeticCircuit a f) where
    toJSON r = object
        [
            "system" .= acSystem r,
            "input"  .= acInput r,
            "output" .= acOutput r,
            "order"  .= acVarOrder r
        ]

-- TODO: properly restore the witness generation function
-- TODO: Check that there are exactly N outputs
instance (FromJSON a, FromJSON (f Natural)) => FromJSON (ArithmeticCircuit a f) where
    parseJSON =
        withObject "ArithmeticCircuit" $ \v -> do
            acSystem   <- v .: "system"
            acRange    <- v .: "range"
            acInput    <- v .: "input"
            acVarOrder <- v .: "order"
            acOutput   <- v .: "output"
            let acWitness = empty
                acRNG     = mkStdGen 0
            pure ArithmeticCircuit{..}
