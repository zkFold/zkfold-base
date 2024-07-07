{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans     #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Control.Monad                                             (foldM, guard, replicateM)
import           Data.Aeson                                                hiding (Bool)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map,
                                                                            null, splitAt, take)
import qualified Data.Map                                                  as Map
import           Data.Traversable                                          (for)
import qualified Data.Zip                                                  as Z
import           GHC.Natural                                               (naturalToInteger)
import           GHC.Num                                                   (integerToInt)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   (Integer, const, fmap, id, max, otherwise,
                                                                            pure, return, show, toInteger, type (~),
                                                                            zip, ($), (++), (.), (<$>), (>>=))
import qualified Prelude                                                   as Haskell
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (arbitrary), Gen, frequency,
                                                                            oneof, vector)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381               (BLS12_381_Scalar)
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (chooseNatural, length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedAll, embedV, embedVarIndex,
                                                                            embedVarIndexV, expansion, foldCircuit,
                                                                            horner, invertC, isZeroC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit, circuitN)
import           ZkFold.Symbolic.Compiler.Arithmetizable                   (SymbolicData (..))
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.DiscreteField
import           ZkFold.Symbolic.Data.Eq

------------------------------------- Instances -------------------------------------

instance Arithmetic a => SymbolicData a (ArithmeticCircuit n a) where
    type TypeSize a (ArithmeticCircuit n a) = n

    pieces = id

    restore = ArithmeticCircuit

-- TODO: I had to add these constraints and I don't like them
instance
    ( KnownNat (n * Order a)
    , KnownNat (Log2 ((n * Order a) - 1) + 1)
    ) => Finite (ArithmeticCircuit n a) where
    type Order (ArithmeticCircuit n a) = n * Order a

instance Arithmetic a => AdditiveSemigroup (ArithmeticCircuit n a) where
    r1 + r2 = circuitN $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i + x j)

instance (Arithmetic a, Scale c a) => Scale c (ArithmeticCircuit n a) where
    scale c r = circuitN $ do
        is <- runCircuit r
        for is $ \i -> newAssigned (\x -> (c `scale` one :: a) `scale` x i)

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (ArithmeticCircuit n a) where
    zero = circuitN $ Vector <$> replicateM (Haskell.fromIntegral $ value @n) (newAssigned (const zero))

instance (Arithmetic a, KnownNat n) => AdditiveGroup (ArithmeticCircuit n a) where
    negate r = circuitN $ do
        is <- runCircuit r
        for is $ \i -> newAssigned (\x -> negate (x i))

    r1 - r2 = circuitN $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i - x j)

instance Arithmetic a => MultiplicativeSemigroup (ArithmeticCircuit n a) where
    r1 * r2 = circuitN $ do
        is <- runCircuit r1
        js <- runCircuit r2
        for (Z.zip is js) $ \(i, j) -> newAssigned (\x -> x i * x j)

instance (Arithmetic a, KnownNat n) => Exponent (ArithmeticCircuit n a) Natural where
    (^) = natPow

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (ArithmeticCircuit n a) where
    one = embedV (pure one)

-- TODO: The constant will be replicated in all outputs. Is this the desired behaviour?
instance (Arithmetic a, FromConstant b a, KnownNat n) => FromConstant b (ArithmeticCircuit n a) where
    fromConstant c = embedAll (fromConstant c)

instance (Arithmetic a, KnownNat n) => Semiring (ArithmeticCircuit n a)

instance (Arithmetic a, KnownNat n) => Ring (ArithmeticCircuit n a)

instance (Arithmetic a, KnownNat n) => Exponent (ArithmeticCircuit n a) Integer where
    (^) = intPowF

instance (Arithmetic a, KnownNat n) => Field (ArithmeticCircuit n a) where
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
instance Arithmetic a => BinaryExpansion (ArithmeticCircuit 1 a) where
    type Bits (ArithmeticCircuit 1 a) = ArithmeticCircuit (NumberOfBits a) a
    binaryExpansion r = circuitN $ do
        output <- runCircuit r
        bits <- expansion (numberOfBits @a) . V.item $ output
        pure $ V.unsafeToVector bits
    fromBinary bits = circuit $ runCircuit bits >>= horner . V.fromVector

instance (Arithmetic a, KnownNat n) => DiscreteField' (ArithmeticCircuit n a) where
    equal r1 r2 = isZeroC (r1 - r2)

instance Arithmetic a => TrichotomyField (ArithmeticCircuit 1 a) where
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

instance Arithmetic a => SymbolicData a (Bool (ArithmeticCircuit n a)) where
    type TypeSize a (Bool (ArithmeticCircuit n a)) = n
    pieces (Bool b) = pieces b
    restore c = Bool Haskell.. restore c

instance (Arithmetic a, KnownNat n, 1 <= n) => DiscreteField (Bool (ArithmeticCircuit 1 a)) (ArithmeticCircuit n a) where
    isZero x = Bool $ circuit $ do
        bools <- runCircuit $ isZeroC x
        foldM (\i j -> newAssigned (\p -> p i * p j)) (V.head bools) (V.tail bools)

instance (Arithmetic a, KnownNat n, 1 <= n) => Eq (Bool (ArithmeticCircuit 1 a)) (ArithmeticCircuit n a) where
    x == y = isZero (x - y)
    x /= y = not $ isZero (x - y)

instance {-# OVERLAPPING #-} (SymbolicData a x, n ~ TypeSize a x, KnownNat n) => Conditional (Bool (ArithmeticCircuit 1 a)) x where
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

-- TODO: make a proper implementation of Arbitrary
instance (Arithmetic a, KnownNat n, Arbitrary a) => Arbitrary (ArithmeticCircuit n a) where
    arbitrary = (ArithmeticCircuit { acCircuit = mempty {acInput = [ 1 ]}, acOutput = pure 1} * ) <$> arbitrary' 0 0 (value @n)

arbitrary' :: forall a n . (Arithmetic a, KnownNat n, Arbitrary a, FromConstant a a) => Natural -> Natural ->  Natural -> Gen (ArithmeticCircuit n a)
arbitrary' inp out outMax
    | out Haskell.== outMax = return $ ArithmeticCircuit { acCircuit = mempty, acOutput = pure outMax}
    | otherwise  = let
        arbVar = do
            arbInp <- chooseNatural (0 , inp)
            arbOut <- chooseNatural (0 , out)
            return $ (embedVarIndex arbInp) { acOutput    = pure arbOut}
        newInp = embedVarIndexV $ inp + 1
        newOut = withOutputs mempty (pure $ out + 1)
        constant = embedV . V.unsafeToVector <$> vector (integerToInt . toInteger $ value @n)

        newVars = [
            newInp
            , newOut
            ]

        la = frequency $ (1, arbVar) : (1, constant) : fmap ((3, ) . return) newVars

        in do
            l <- la
            let inp' =  max (length $ inputVariables l) inp
            let out' =  max (length $ acOutput l) out
            r <- arbitrary' inp' out' outMax
            oneof $ fmap return [
                l + r
                , l * r
                , l - r
                , r - l
                , l // r
                , r // l
                ]




        -- | Haskell.otherwise  = return ArithmeticCircuit { acCircuit = mempty, acOutput = pure $ integerToNatural outMax}




-- TODO: make it more readable
instance (FiniteField a, Haskell.Eq a, Haskell.Show a) => Haskell.Show (ArithmeticCircuit n a) where
    show (ArithmeticCircuit r o) = "ArithmeticCircuit { acInput = "
        ++ show (acInput r) ++ ", acSystem = " ++ show (acSystem r) ++ ", acOutput = " ++ show o ++ ", acVarOrder = " ++ show (acVarOrder r) ++ " }"

-- TODO: add witness generation info to the JSON object
instance ToJSON a => ToJSON (ArithmeticCircuit n a) where
    toJSON (ArithmeticCircuit r o) = object
        [
            "system" .= acSystem r,
            "input"  .= acInput r,
            "output" .= V.fromVector o,
            "order"  .= acVarOrder r
        ]

-- TODO: properly restore the witness generation function
-- TODO: Check that there are exactly N outputs
instance (FromJSON a, KnownNat n) => FromJSON (ArithmeticCircuit n a) where
    parseJSON =
        withObject "ArithmeticCircuit" $ \v -> do
            acSystem <- v .: "system"
            acInput <- v .: "input"
            let acWitness = const empty
            outs <- v .: "output"
            guard (length v == (value @n))
            let acOutput = Vector outs
            acVarOrder <- v .: "order"
            let acRNG = mkStdGen 0
                acCircuit = Circuit{..}
            pure ArithmeticCircuit{..}

type F = Zp BLS12_381_Scalar
data (Arithmetic a, KnownNat n) => ArithmeticCircuitTest n a = ArithmeticCircuitTest
    {
        arithmeticCircuit :: ArithmeticCircuit n a
        , witnessInput    :: Map.Map Natural F
    }

instance (Arithmetic a, KnownNat n, Arbitrary a) => Arbitrary (ArithmeticCircuitTest n a) where
    arbitrary :: Gen (ArithmeticCircuitTest n a)
    arbitrary = do
        ac <- arbitrary
        let keysAC = inputVariables ac
        let len = length keysAC
        values <- vector (integerToInt $ naturalToInteger len)
        let wi = fromList $ zip keysAC values
        return ArithmeticCircuitTest {
            arithmeticCircuit = ac
            , witnessInput = wi
            }
