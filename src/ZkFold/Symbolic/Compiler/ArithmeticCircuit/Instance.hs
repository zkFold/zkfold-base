{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Control.Monad.State                                    (MonadState (..), evalState, execState)
import           Data.Aeson
import           Data.List                                              (nub)
import           Data.Map                                               hiding (drop,foldl,foldr, map, null, splitAt, take)
import           Prelude                                                hiding (Num (..), drop, length, product, splitAt, sum, take, (!!), (^))
import qualified Prelude                                                as Haskell
import           System.Random                                          (mkStdGen, uniform)
import           Test.QuickCheck                                        (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate           (monomial, polynomial)
import           ZkFold.Prelude                                         ((!!))

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (invertC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.Arithmetizable                (Arithmetizable (..))

------------------------------------- Instances -------------------------------------

instance Eq a => Semigroup (ArithmeticCircuit a) where
    r1 <> r2 = ArithmeticCircuit
        {
            acSystem   = acSystem r1 `union` acSystem r2,
            -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
            -- We need a way to ensure the correct order no matter how `(<>)` is used.
            acInput    = nub $ acInput r1 ++ acInput r2,
            acWitness  = \w -> acWitness r1 w `union` acWitness r2 w,
            acOutput   = max (acOutput r1) (acOutput r2),
            acVarOrder = acVarOrder r1 `union` acVarOrder r2,
            acRNG      = mkStdGen $ fst (uniform (acRNG r1)) Haskell.* fst (uniform (acRNG r2))
        }

instance (FiniteField a, Eq a) => Monoid (ArithmeticCircuit a) where
    mempty = ArithmeticCircuit
        {
            acSystem   = empty,
            acInput    = [],
            acWitness  = insert 0 one,
            acOutput   = 0,
            acVarOrder = empty,
            acRNG      = mkStdGen 0
        }

instance (FiniteField a, Eq a, ToBits a) => Arithmetizable a (ArithmeticCircuit a) where
    arithmetize r = do
        r' <- get
        let r'' = r <> r' { acOutput = acOutput r }
        put r''
        return [r'']

    restore [r] = r
    restore _   = error "restore ArithmeticCircuit: wrong number of arguments"

    typeSize = 1

instance FiniteField a => Finite (ArithmeticCircuit a) where
    order = order @a

instance (FiniteField a, Eq a, ToBits a) => AdditiveSemigroup (ArithmeticCircuit a) where
    r1 + r2 = flip execState (r1 <> r2) $ do
        let x1  = acOutput r1
            x2  = acOutput r2
            con = \z -> polynomial [
                            monomial one (singleton x1 one),
                            monomial one (singleton x2 one),
                            monomial (negate one) (singleton z one)
                        ]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (eval r1 + eval r2)

instance (FiniteField a, Eq a, ToBits a) => AdditiveMonoid (ArithmeticCircuit a) where
    zero = flip execState mempty $ do
        let con = \z -> polynomial [monomial one (singleton z one)]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment zero

instance (FiniteField a, Eq a, ToBits a) => AdditiveGroup (ArithmeticCircuit a) where
    negate r = flip execState r $ do
        let x   = acOutput r
            con = \z -> polynomial [
                            monomial one (singleton x one),
                            monomial one (singleton z one)
                        ]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (negate $ eval r)

    r1 - r2 = flip execState (r1 <> r2) $ do
        let x1    = acOutput r1
            x2    = acOutput r2
            con z =
                polynomial [
                    monomial one (singleton x1 one),
                    monomial (negate one) (singleton x2 one),
                    monomial (negate one) (singleton z one)
                ]
        z <- newVariableFromConstraint con
        addVariable z
        constraint (con z)
        assignment (eval r1 - eval r2)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeSemigroup (ArithmeticCircuit a) where
    r1 * r2 = flip execState (r1 <> r2) $ do
        let x1  = acOutput r1
            x2  = acOutput r2
            con = \z -> polynomial [
                            monomial one (fromListWith (+) [(x1, one), (x2, one)]),
                            monomial (negate one) (singleton z one)
                        ]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (eval r1 * eval r2)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeMonoid (ArithmeticCircuit a) where
    one = mempty

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeGroup (ArithmeticCircuit a) where
    invert = invertC

instance (FiniteField a, Eq a, ToBits a, FromConstant b a) => FromConstant b (ArithmeticCircuit a) where
    fromConstant c = flip execState mempty $ do
        let x = fromConstant c
            con = \z -> polynomial [monomial one (singleton z one), monomial (negate x) (singleton 0 one)]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (const x)

instance (FiniteField a, Eq a, ToBits a) => ToBits (ArithmeticCircuit a) where
    toBits x =
        let two = one + one
            ps  = map (two ^) [0.. numberOfBits @a - 1]
            f z = flip evalState z $ mapM (\i -> do
                    x' <- newVariable
                    addVariable x'
                    assignment ((!! i) . padBits (numberOfBits @a) . toBits . eval x)
                    constraint $ polynomial [monomial one (singleton x' (one + one)), monomial (negate one) (singleton x' one)]
                    get
                ) [0.. numberOfBits @a - 1]
            v z = z - sum (zipWith (*) (f z) ps)
            y   = x { acRNG = acRNG (v x) }
            bs  = map acOutput $ f y
            r   = execState forceZero $ v y
        in map (\x'' -> r { acOutput = x'' } ) bs

-- TODO: make a proper implementation of Arbitrary
instance (FiniteField a, Eq a, ToBits a) => Arbitrary (ArithmeticCircuit a) where
    arbitrary = do
        let ac = mempty { acOutput = 1} * mempty { acOutput = 2}
        return ac

-- TODO: make it more readable
instance (FiniteField a, Eq a, ToBits a, Show a) => Show (ArithmeticCircuit a) where
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
