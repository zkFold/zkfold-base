{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Control.Monad.State                                    (MonadState (..), execState, runState)
import           Data.Aeson
import           Data.List                                              (foldl')
import           Data.Map                                               hiding (drop, foldl, foldl', foldr, map, null, splitAt, take)
import           Data.Traversable                                       (for)
import           Prelude                                                hiding (Num (..), drop, length, product, splitAt, sum, take, (!!), (^))
import           System.Random                                          (mkStdGen)
import           Test.QuickCheck                                        (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate           (monomial, polynomial)
import           ZkFold.Prelude                                         ((!!))

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (invertC, mappendC, plusMultC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.Arithmetizable                (Arithmetizable (..))

------------------------------------- Instances -------------------------------------

instance Eq a => Semigroup (ArithmeticCircuit a) where
    (<>) = mappendC

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

instance Arithmetic a => Arithmetizable a (ArithmeticCircuit a) where
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

instance Arithmetic a => AdditiveSemigroup (ArithmeticCircuit a) where
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

instance Arithmetic a => AdditiveMonoid (ArithmeticCircuit a) where
    zero = flip execState mempty $ do
        let con = \z -> polynomial [monomial one (singleton z one)]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment zero

instance Arithmetic a => AdditiveGroup (ArithmeticCircuit a) where
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

instance Arithmetic a => MultiplicativeSemigroup (ArithmeticCircuit a) where
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

instance Arithmetic a => MultiplicativeMonoid (ArithmeticCircuit a) where
    one = mempty

instance Arithmetic a => MultiplicativeGroup (ArithmeticCircuit a) where
    invert = invertC

instance (Arithmetic a, FromConstant b a) => FromConstant b (ArithmeticCircuit a) where
    fromConstant c = flip execState mempty $ do
        let x = fromConstant c
            con = \z -> polynomial [monomial one (singleton z one), monomial (negate x) (singleton 0 one)]
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (const x)

instance Arithmetic a => ToBits (ArithmeticCircuit a) where
    toBits x =
        let repr       = padBits (numberOfBits @a) . toBits . eval x
            boolCon b  = polynomial [
                             monomial one (singleton b (one + one)),
                             monomial (negate one) (singleton b one)
                         ]
            (bits, x') = flip runState x . for [0 .. numberOfBits @a - 1] $ \i -> do
                b <- newVariableWithSource [acOutput x] boolCon
                addVariable b
                assignment ((!! i) . repr)
                constraint (boolCon b)
                return b
         in case bits of
            []       -> []
            (b : bs) -> let two         = one + one
                            f (y, p) b' = (plusMultC y (x' { acOutput = b' }) p, p * two)
                            (x'', _)    = foldl' f (x' { acOutput = b }, two) bs
                            constrained = flip execState x'' $ constraint
                                $ polynomial [
                                      monomial one (singleton (acOutput x) one),
                                      monomial (negate one) (singleton (acOutput x'') one)
                                  ]
                         in [ constrained { acOutput = b' } | b' <- b : bs ]

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
