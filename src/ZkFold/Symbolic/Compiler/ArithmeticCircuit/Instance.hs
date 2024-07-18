{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Control.Monad                                             (foldM, guard, replicateM)
import           Data.Aeson                                                hiding (Bool)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map,
                                                                            null, splitAt, take)
import           Data.Traversable                                          (for)
import qualified Data.Zip                                                  as Z
import           GHC.Num                                                   (integerToNatural)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   (Integer, Show, const, id, mempty, pure,
                                                                            return, show, type (~), ($), (++), (.),
                                                                            (<$>), (>>=))
import qualified Prelude                                                   as Haskell
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (arbitrary), Gen, chooseInteger,
                                                                            elements)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (length)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedAll, embedV, expansion, foldCircuit,
                                                                            getAllVars, horner, invertC, isZeroC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit, circuitN)
import           ZkFold.Symbolic.Compiler.Arithmetizable                   (Arithmetizable, SymbolicData (..))
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.DiscreteField
import           ZkFold.Symbolic.Data.Eq

------------------------------------- Instances -------------------------------------

instance Symbolic (ArithmeticCircuit a) where
    type BaseField (ArithmeticCircuit a) = a

instance Arithmetic a => SymbolicData a (ArithmeticCircuit a n) where
    type TypeSize a (ArithmeticCircuit a n) = n

    pieces = id

    restore = ArithmeticCircuit

deriving newtype instance Arithmetic a => SymbolicData a (Bool (ArithmeticCircuit a))
deriving newtype instance Arithmetic a => Arithmetizable a (Bool (ArithmeticCircuit a))

-- TODO: I had to add these constraints and I don't like them
instance
    ( KnownNat (n * Order a)
    , KnownNat (Log2 (n * Order a - 1) + 1)
    ) => Finite (ArithmeticCircuit a n) where
    type Order (ArithmeticCircuit a n) = n * Order a

instance Arithmetic a => AdditiveSemigroup (ArithmeticCircuit a n) where
    r1 + r2 = circuitN $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i + x j)

instance (Arithmetic a, Scale c a) => Scale c (ArithmeticCircuit a n) where
    scale c r = circuitN $ do
        is <- runCircuit r
        for is $ \i -> newAssigned (\x -> (c `scale` one :: a) `scale` x i)

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (ArithmeticCircuit a n) where
    zero = circuitN $ Vector <$> replicateM (Haskell.fromIntegral $ value @n) (newAssigned (const zero))

instance (Arithmetic a, KnownNat n) => AdditiveGroup (ArithmeticCircuit a n) where
    negate r = circuitN $ do
        is <- runCircuit r
        for is $ \i -> newAssigned (\x -> negate (x i))

    r1 - r2 = circuitN $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i - x j)

instance Arithmetic a => MultiplicativeSemigroup (ArithmeticCircuit a n) where
    r1 * r2 = circuitN $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i * x j)

instance (Arithmetic a, KnownNat n) => Exponent (ArithmeticCircuit a n) Natural where
    (^) = natPow

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (ArithmeticCircuit a n) where
    one = embedV (pure one)

-- TODO: The constant will be replicated in all outputs. Is this the desired behaviour?
instance (Arithmetic a, FromConstant b a, KnownNat n) => FromConstant b (ArithmeticCircuit a n) where
    fromConstant c = embedAll (fromConstant c)

instance (Arithmetic a, KnownNat n) => Semiring (ArithmeticCircuit a n)

instance (Arithmetic a, KnownNat n) => Ring (ArithmeticCircuit a n)

instance (Arithmetic a, KnownNat n) => Exponent (ArithmeticCircuit a n) Integer where
    (^) = intPowF

instance (Arithmetic a, KnownNat n) => Field (ArithmeticCircuit a n) where
    finv = invertC
    rootOfUnity n = embedAll <$> rootOfUnity n

-- TODO: The only implementation that seems to make sense is when there is only one output.
-- It is true?
--
-- Anyway, @binaryExpansion@ of an arithmetic circuit will return copies of the same circuit with different outputs.
-- The whole point of this refactor was to avoid this.
--
-- Ideally, we want to return another ArithmeticCircuit with a number of outputs corresponding to the number of bits.
-- This does not align well with the type of @binaryExpansion@
instance Arithmetic a => BinaryExpansion (ArithmeticCircuit a 1) where
    type Bits (ArithmeticCircuit a 1) = ArithmeticCircuit a (NumberOfBits a)
    binaryExpansion r = circuitN $ do
        output <- runCircuit r
        bits   <- expansion (numberOfBits @a) . V.item $ output
        pure $ V.unsafeToVector bits
    fromBinary bits = circuit $ runCircuit bits >>= horner . V.fromVector

instance (Arithmetic a, KnownNat n) => DiscreteField' (ArithmeticCircuit a n) where
    equal r1 r2 = isZeroC (r1 - r2)

instance Arithmetic a => TrichotomyField (ArithmeticCircuit a 1) where
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

instance (Arithmetic a, KnownNat n, 1 <= n) => DiscreteField (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a n) where
    isZero x = Bool $ circuit $ do
        bools <- runCircuit $ isZeroC x
        foldM (\i j -> newAssigned (\p -> p i * p j)) (V.head bools) (V.tail bools)

instance (Arithmetic a, KnownNat n, 1 <= n) => Eq (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a n) where
    x == y = isZero (x - y)
    x /= y = not $ isZero (x - y)

instance (SymbolicData a x, n ~ TypeSize a x, KnownNat n) => Conditional (Bool (ArithmeticCircuit a)) x where
    bool brFalse brTrue (Bool b) = restore c o
        where
            f' = pieces brFalse
            t' = pieces brTrue
            ArithmeticCircuit c o = circuitN solve

            solve :: forall i m . MonadBlueprint i a m => m (Vector n i)
            solve = do
                ts <- runCircuit t'
                fs <- runCircuit f'
                bs <- V.item <$> runCircuit b
                V.zipWithM (\x y -> newAssigned $ \p -> p bs * (p x - p y) + p y) ts fs

instance (Arithmetic a, Arbitrary a) => Arbitrary (ArithmeticCircuit a 1) where
    arbitrary = do
        k <- integerToNatural <$> chooseInteger (2, 10)
        let ac = ArithmeticCircuit { acCircuit = mempty {acInput = [1..k]}, acOutput = pure k }
        arbitrary' ac 10

arbitrary' :: forall a . (Arithmetic a, Arbitrary a, FromConstant a a) => ArithmeticCircuit a 1 -> Natural -> Gen (ArithmeticCircuit a 1)
arbitrary' ac 0 = return ac
arbitrary' ac iter = do
    let vars = getAllVars . acCircuit $ ac
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
instance (FiniteField a, Haskell.Eq a, Show a) => Show (ArithmeticCircuit a n) where
    show (ArithmeticCircuit r o) = "ArithmeticCircuit { acInput = " ++ show (acInput r)
        ++ "\n, acSystem = " ++ show (acSystem r) ++ "\n, acOutput = " ++ show o ++ "\n, acVarOrder = " ++ show (acVarOrder r) ++ " }"

-- TODO: add witness generation info to the JSON object
instance ToJSON a => ToJSON (ArithmeticCircuit a n) where
    toJSON (ArithmeticCircuit r o) = object
        [
            "system" .= acSystem r,
            "input"  .= acInput r,
            "output" .= V.fromVector o,
            "order"  .= acVarOrder r
        ]

-- TODO: properly restore the witness generation function
-- TODO: Check that there are exactly N outputs
instance (FromJSON a, KnownNat n) => FromJSON (ArithmeticCircuit a n) where
    parseJSON =
        withObject "ArithmeticCircuit" $ \v -> do
            acSystem   <- v .: "system"
            acRange    <- v .: "range"
            acInput    <- v .: "input"
            acVarOrder <- v .: "order"
            outs       <- v .: "output"
            guard (length v Haskell.== value @n)
            let acWitness = empty
                acRNG     = mkStdGen 0
                acOutput  = Vector outs
                acCircuit = Circuit{..}
            pure ArithmeticCircuit{..}
