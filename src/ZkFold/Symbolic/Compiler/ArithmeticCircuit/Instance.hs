{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson
import           Data.Foldable                                             (foldrM)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map, null, splitAt, take)
import           Data.Traversable                                          (for)
import           Prelude                                                   hiding (Num (..), drop, length, product, splitAt, sum, take, (!!), (^))
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                            ((!!))

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (invertC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint(..), circuit, circuits)
import           ZkFold.Symbolic.Compiler.Arithmetizable                   (Arithmetizable (..))

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
    fromConstant c = circuit $ newAssigned $ const (fromConstant @b @a c `scale` one)

instance Arithmetic a => ToBits (ArithmeticCircuit a) where
    toBits r = circuits $ do
        k <- runCircuit r
        let repr = padBits (numberOfBits @a) . toBits . ($ k)
        bits <- for [0 .. numberOfBits @a - 1] $ \j -> do
            newSourced [k] (\x i -> x i * (x i - one)) ((!! j) . repr)
        case reverse bits of
            [] -> return []
            (b : bs) -> do
                let two = one + one :: a
                k' <- foldrM (\i s -> newAssigned $ \x -> x i + (two `scale` x s)) b bs
                constraint (\x -> x k - x k')
                return bits

-- TODO: make a proper implementation of Arbitrary
instance Arithmetic a => Arbitrary (ArithmeticCircuit a) where
    arbitrary = do
        let ac = mempty { acOutput = 1} * mempty { acOutput = 2}
        return ac

-- TODO: make it more readable
instance (FiniteField a, Eq a, Show a) => Show (ArithmeticCircuit a) where
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
