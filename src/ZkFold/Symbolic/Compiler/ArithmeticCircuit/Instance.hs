{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson                                                hiding (Bool)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map,
                                                                            null, splitAt, take)
import           Data.Zip                                                  (zipWith)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   (Integer, const, error, mempty, pure, return,
                                                                            show, ($), (++), (<$>), (<*>), (>>=))
import qualified Prelude                                                   as Haskell
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embed, expansion, horner, invertC, isZeroC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit, circuits)
import           ZkFold.Symbolic.Compiler.Arithmetizable                   (SymbolicData (..))
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.DiscreteField
import           ZkFold.Symbolic.Data.Eq

------------------------------------- Instances -------------------------------------

instance Arithmetic a => SymbolicData a (ArithmeticCircuit a) where
    pieces r = [r]

    restore [r] = r
    restore _   = error "restore ArithmeticCircuit: wrong number of arguments"

    typeSize = 1

instance FiniteField a => Finite (ArithmeticCircuit a) where
    type Order (ArithmeticCircuit a) = Order a

instance Arithmetic a => AdditiveSemigroup (ArithmeticCircuit a) where
    r1 + r2 = circuit $ do
        i <- runCircuit r1
        j <- runCircuit r2
        newAssigned (\x -> x i + x j)

instance (Arithmetic a, Scale c a) => Scale c (ArithmeticCircuit a) where
    scale c r = circuit $ do
        i <- runCircuit r
        newAssigned (\x -> (c `scale` one :: a) `scale` x i)

instance Arithmetic a => AdditiveMonoid (ArithmeticCircuit a) where
    zero = circuit $ newAssigned (const zero)

instance Arithmetic a => AdditiveGroup (ArithmeticCircuit a) where
    negate r = circuit $ do
        i <- runCircuit r
        newAssigned (\x -> negate (x i))

    r1 - r2 = circuit $ do
        i <- runCircuit r1
        j <- runCircuit r2
        newAssigned (\x -> x i - x j)

instance Arithmetic a => MultiplicativeSemigroup (ArithmeticCircuit a) where
    r1 * r2 = circuit $ do
        i <- runCircuit r1
        j <- runCircuit r2
        newAssigned (\x -> x i * x j)

instance Arithmetic a => Exponent (ArithmeticCircuit a) Natural where
    (^) = natPow

instance Arithmetic a => MultiplicativeMonoid (ArithmeticCircuit a) where
    one = mempty

instance (Arithmetic a, FromConstant b a) => FromConstant b (ArithmeticCircuit a) where
    fromConstant c = embed (fromConstant c)

instance Arithmetic a => Semiring (ArithmeticCircuit a)

instance Arithmetic a => Ring (ArithmeticCircuit a)

instance Arithmetic a => Exponent (ArithmeticCircuit a) Integer where
    (^) = intPowF

instance Arithmetic a => Field (ArithmeticCircuit a) where
    finv = invertC
    rootOfUnity n = embed <$> rootOfUnity n

instance Arithmetic a => BinaryExpansion (ArithmeticCircuit a) where
    binaryExpansion r = circuits $ runCircuit r >>= expansion (numberOfBits @a)
    fromBinary bits = circuit $ Haskell.traverse runCircuit bits >>= horner

instance Arithmetic a => DiscreteField' (ArithmeticCircuit a) where
    equal r1 r2 = isZeroC (r1 - r2)

instance Arithmetic a => TrichotomyField (ArithmeticCircuit a) where
    trichotomy r1 r2 =
        let
            bits1 = binaryExpansion r1
            bits2 = binaryExpansion r2
            zipWith0 _ [] []         = []
            zipWith0 f [] ys         = zipWith0 f [zero] ys
            zipWith0 f xs []         = zipWith0 f xs [zero]
            zipWith0 f (x:xs) (y:ys) = f x y : zipWith0 f xs ys
            -- zip pairs of bits in {0,1} to orderings in {-1,0,1}
            comparedBits = zipWith0 (-) bits1 bits2
            -- least significant bit first,
            -- reverse lexicographical ordering
            reverseLexicographical x y = y * y * (y - x) + x
        in
            Haskell.foldl reverseLexicographical zero comparedBits

instance Arithmetic a => SymbolicData a (Bool (ArithmeticCircuit a)) where
    pieces (Bool b) = pieces b
    restore = Bool Haskell.. restore
    typeSize = 1

instance Arithmetic a => DiscreteField (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a) where
    isZero x = Bool (isZeroC x)

instance Arithmetic a => Eq (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a) where
    x == y = isZero (x - y)
    x /= y = not $ isZero (x - y)

instance {-# OVERLAPPING #-} SymbolicData a x => Conditional (Bool (ArithmeticCircuit a)) x where
    bool brFalse brTrue (Bool b) =
        let f' = pieces brFalse
            t' = pieces brTrue
        in restore $ zipWith (\f t -> b * (t - f) + f) f' t'

-- TODO: make a proper implementation of Arbitrary
instance Arithmetic a => Arbitrary (ArithmeticCircuit a) where
    arbitrary = do
        let ac = mempty { acOutput = 1} * mempty { acOutput = 2}
        return ac

-- TODO: make it more readable
instance (FiniteField a, Haskell.Eq a, Haskell.Show a) => Haskell.Show (ArithmeticCircuit a) where
    show r = "ArithmeticCircuit { acSystem = " ++ show (acSystem r) ++ ", acInput = "
        ++ show (acInput r) ++ ", acOutput = " ++ show (acOutput r) ++ ", acVarOrder = " ++ show (acVarOrder r) ++ " }"

-- TODO: add witness generation info to the JSON object
instance ToJSON a => ToJSON (ArithmeticCircuit a) where
    toJSON r = object
        [
            "system" .= acSystem r,
            "input"  .= acInput r,
            "output" .= acOutput r,
            "order"  .= acVarOrder r
        ]

-- TODO: properly restore the witness generation function
instance FromJSON a => FromJSON (ArithmeticCircuit a) where
    parseJSON = withObject "ArithmeticCircuit" $ \v -> ArithmeticCircuit
        <$> v .: "system"
        <*> v .: "input"
        <*> pure (const empty)
        <*> v .: "output"
        <*> v .: "order"
        <*> pure (mkStdGen 0)
