{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson                                          hiding (Bool)
import           Data.Containers.ListUtils                           (nubOrd)
import           Data.List                                           (sort)
import           Data.Map                                            hiding (drop, foldl, foldl', foldr, map, null,
                                                                      splitAt, take, toList)
import           GHC.Generics                                        (Par1 (..))
import           GHC.IsList                                          (IsList (..))
import           GHC.Num                                             (integerToNatural)
import           Prelude                                             (Show, concatMap, mempty, pure, return, show, ($),
                                                                      (++), (.), (<$>))
import qualified Prelude                                             as Haskell
import           System.Random                                       (mkStdGen)
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen, chooseInteger,
                                                                      elements)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (variables)
import           ZkFold.Base.Data.Par1                               ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal hiding (constraint)
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement (..))

------------------------------------- Instances -------------------------------------

instance (Arithmetic a, Arbitrary a) => Arbitrary (ArithmeticCircuit a Par1) where
    arbitrary = do
        k <- integerToNatural <$> chooseInteger (2, 10)
        let ac = mempty { acInput = [1..k], acOutput = pure k }
        fromFieldElement <$> arbitrary' (FieldElement ac) 10

getAllVars :: MultiplicativeMonoid a => ArithmeticCircuit a o -> [Natural]
getAllVars ac = nubOrd $ sort $ 0 : acInput ac ++ concatMap (toList . variables) (elems $ acSystem ac)

arbitrary' :: forall a . (Arithmetic a, Arbitrary a, FromConstant a a) => FieldElement (ArithmeticCircuit a) -> Natural -> Gen (FieldElement (ArithmeticCircuit a))
arbitrary' ac 0 = return ac
arbitrary' ac iter = do
    let vars = getAllVars (fromFieldElement ac)
    li <- elements vars
    ri <- elements vars
    let (l, r) = ( FieldElement (fromFieldElement ac) { acOutput = pure li }
                 , FieldElement (fromFieldElement ac) { acOutput = pure ri })
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
