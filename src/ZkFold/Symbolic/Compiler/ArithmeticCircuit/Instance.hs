{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson                                                hiding (Bool)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map, null, splitAt, take)
import           Prelude                                                   (const, error, map, mempty, pure, return, show, zipWith, ($), (++), (<$>), (<*>), (>>=))
import qualified Prelude                                                   as Haskell
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embed, expansion, horner, invertC, isZeroC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit, circuits)
import           ZkFold.Symbolic.Compiler.Arithmetizable                   (Arithmetizable (..))
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.DiscreteField
import           ZkFold.Symbolic.Data.Eq

------------------------------------- Instances -------------------------------------

instance Arithmetic a => Arithmetizable a (ArithmeticCircuit a) where
    arithmetize r = pure <$> runCircuit r

    restore [r] = r
    restore _   = error "restore ArithmeticCircuit: wrong number of arguments"

    typeSize = 1

instance FiniteField a => Finite (ArithmeticCircuit a) where
    order = order @a

instance Arithmetic a => AdditiveSemigroup (ArithmeticCircuit a) where
    r1 + r2 = circuit $ do
        i <- runCircuit r1
        j <- runCircuit r2
        newAssigned (\x -> x i + x j)

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

instance Arithmetic a => MultiplicativeMonoid (ArithmeticCircuit a) where
    one = mempty

instance Arithmetic a => MultiplicativeGroup (ArithmeticCircuit a) where
    invert = invertC

instance (Arithmetic a, FromConstant b a) => FromConstant b (ArithmeticCircuit a) where
    fromConstant c = embed (fromConstant c)

instance Arithmetic a => Ring (ArithmeticCircuit a)

instance Arithmetic a => BinaryExpansion (ArithmeticCircuit a) where
    binaryExpansion r = circuits $ runCircuit r >>= expansion (numberOfBits @a)
    fromBinary bits = circuit $ Haskell.traverse runCircuit bits >>= horner

instance Arithmetic a => Arithmetizable a (Bool (ArithmeticCircuit a)) where
    arithmetize (Bool b) = arithmetize b

    restore [r] = Bool $ restore [r]
    restore _   = error "SymbolicBool: invalid number of values"

    typeSize = 1

instance (Arithmetizable a x, Field x) => DiscreteField (Bool (ArithmeticCircuit a)) x where
    isZero x = case circuits (arithmetize x) of
      [] -> true
      xs -> Bool $ product1 (map isZeroC xs)

instance Arithmetic a => Eq (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a) where
    x == y = isZero (x - y)
    x /= y = not $ isZero (x - y)

instance Arithmetizable a x => Conditional (Bool (ArithmeticCircuit a)) x where
    bool brFalse brTrue (Bool b) =
        let f' = circuits (arithmetize brFalse)
            t' = circuits (arithmetize brTrue)
        in restore $ zipWith (\f t -> b * t + (one - b) * f) f' t'

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
