{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson                                                hiding (Bool)
import           Data.Foldable                                             (foldl', null)
import           Data.Map                                                  hiding (drop, foldl, foldl', foldr, map, null, splitAt, take)
import           Data.Traversable                                          (for)
import           Prelude                                                   (const, error, map, mempty, pure, return, reverse, show, zipWith, ($), (++), (.), (<$>), (<*>))
import qualified Prelude                                                   as Haskell
import           System.Random                                             (mkStdGen)
import           Test.QuickCheck                                           (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                            ((!!))

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embed, invertC, isZeroC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       hiding (constraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint(..), circuit, circuits)
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

instance Arithmetic a => BinaryExpansion (ArithmeticCircuit a) where
    binaryExpansion r = if numberOfBits @a Haskell.== 0 then [] else circuits $ do
        k <- runCircuit r
        bits <- for [0 .. numberOfBits @a - 1] $ \j -> do
            newConstrained (\x i -> x i * (x i - one)) ((!! j) . repr . ($ k))
        outputs <- for bits output
        k' <- runCircuit (fromBinary outputs)
        constraint (\x -> x k - x k')
        return bits
        where
          repr :: forall b . (BinaryExpansion b, Finite b) => b -> [b]
          repr = padBits (numberOfBits @b) . binaryExpansion

    fromBinary bits =
        case reverse bits of
            [] -> zero
            (b : bs) -> foldl' gorner b bs
        where gorner s b = circuit $ do
                i <- runCircuit s
                j <- runCircuit b
                newAssigned (\x -> x i + x i + x j)

instance Arithmetic a => Arithmetizable a (Bool (ArithmeticCircuit a)) where
    arithmetize (Bool b) = arithmetize b

    restore [r] = Bool $ restore [r]
    restore _   = error "SymbolicBool: invalid number of values"

    typeSize = 1

instance (Arithmetizable a x, Field x) => DiscreteField (Bool (ArithmeticCircuit a)) x where
    isZero x = case circuits (arithmetize x) of
      [] -> true
      xs -> Bool $ product1 (map isZeroC xs)

instance Arithmetizable a x => Eq (Bool (ArithmeticCircuit a)) x where
    x == y =
        let x' = circuits (arithmetize x)
            y' = circuits (arithmetize y)
            zs = zipWith (-) x' y'
        in if null zs
            then true
            else all1 (isZero @(Bool (ArithmeticCircuit a)) @(ArithmeticCircuit a)) zs

    x /= y =
        let x' = circuits (arithmetize x)
            y' = circuits (arithmetize y)
            zs = zipWith (-) x' y'
        in if null zs
            then false
            else not $ all1 (isZero @(Bool (ArithmeticCircuit a)) @(ArithmeticCircuit a)) zs

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
    show r = "ArithmeticCircuit { acSystem = " ++ show (acSystem r)
        ++ ", acInput = " ++ show (acInput r)
        ++ ", acWitness = " ++ show (acWitness r)
        ++ ", acOutput = " ++ show (acOutput r)
        ++ ", acVarOrder = " ++ show (acVarOrder r) ++ " }"

-- TODO: add witness generation info to the JSON object
instance ToJSON a => ToJSON (ArithmeticCircuit a) where
    toJSON r = object
        [
            "system" .= acSystem r,
            "input"  .= acInput r,
            "witness" .= acWitness r,
            "output" .= acOutput r,
            "order"  .= acVarOrder r
        ]

-- TODO: properly restore the witness generation function
instance FromJSON a => FromJSON (ArithmeticCircuit a) where
    parseJSON = withObject "ArithmeticCircuit" $ \v -> ArithmeticCircuit
        <$> v .: "system"
        <*> v .: "input"
        <*> v .: "witness"
        <*> v .: "output"
        <*> v .: "order"
        <*> pure (mkStdGen 0)
