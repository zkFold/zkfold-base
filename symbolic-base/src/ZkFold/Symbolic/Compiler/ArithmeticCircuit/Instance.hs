{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson                                          hiding (Bool)
import           Data.Binary                                         (Binary)
import           Data.Functor.Rep                                    (Representable (..))
import           Data.Map                                            hiding (drop, foldl, foldl', foldr, map, null,
                                                                      splitAt, take, toList)
import           GHC.Generics                                        (Par1 (..))
import           Prelude                                             (Show, mempty, pure, return, show, ($), (++), (.),
                                                                      (<$>))
import qualified Prelude                                             as Haskell
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen, elements)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                             (Vector, unsafeToVector)
import           ZkFold.Prelude                                      (genSubset)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement (..), createRangeConstraint)

------------------------------------- Instances -------------------------------------

instance
  ( Arithmetic a
  , Arbitrary a
  , Binary a
  , Arbitrary (Rep i)
  , Binary (Rep i)
  , Haskell.Ord (Rep i)
  , Representable i
  , Haskell.Foldable i
  ) => Arbitrary (ArithmeticCircuit a i Par1) where
    arbitrary = do
        outVar <- SysVar . InVar <$> arbitrary
        let ac = mempty {acOutput = Par1 outVar}
        -- let ac = createRangeConstraint (FieldElement $ mempty {acOutput = Par1 outVar}) (fromConstant @Natural 1)
        fromFieldElement <$> arbitrary' (FieldElement ac) 10

instance
  ( Arithmetic a
  , Arbitrary a
  , Binary a
  , Arbitrary (Rep i)
  , Binary (Rep i)
  , Haskell.Ord (Rep i)
  , Representable i
  , Haskell.Foldable i
  , KnownNat l
  ) => Arbitrary (ArithmeticCircuit a i (Vector l)) where
    arbitrary = do
        ac <- arbitrary @(ArithmeticCircuit a i Par1)
        o  <- unsafeToVector <$> genSubset (value @l) (getAllVars ac)
        return ac {acOutput = SysVar <$> o}

arbitrary' ::
  forall a i .
  (Arithmetic a, Binary a, Binary (Rep i), Haskell.Ord (Rep i)) =>
  (Representable i, Haskell.Foldable i) =>
  FieldElement (ArithmeticCircuit a i) -> Natural ->
  Gen (FieldElement (ArithmeticCircuit a i))
arbitrary' ac 0 = return ac
arbitrary' ac iter = do
    let vars = getAllVars (fromFieldElement ac)
    li <- elements vars
    ri <- elements vars
    let (l, r) = ( FieldElement (fromFieldElement ac) { acOutput = pure (SysVar li)}
                 , FieldElement (fromFieldElement ac) { acOutput = pure (SysVar ri)})
    let c = FieldElement (fromFieldElement $ createRangeConstraint ac (fromConstant @Natural 10)) { acOutput = pure (SysVar li)}

    ac' <- elements [
        l + r
        , l * r
        , l - r
        , l // r
        , c
        ]
    arbitrary' ac' (iter -! 1)


-- TODO: make it more readable
instance (FiniteField a, Haskell.Eq a, Show a, Show (o (Var a i)), Haskell.Ord (Rep i), Show (Var a i), Show (Rep i)) => Show (ArithmeticCircuit a i o) where
    show r = "ArithmeticCircuit { acSystem = " ++ show (acSystem r)
                          ++ "\n, acRange = " ++ show (acRange r)
                          ++ "\n, acOutput = " ++ show (acOutput r)
                          ++ " }"

-- TODO: add witness generation info to the JSON object
instance (ToJSON a, ToJSON (o (Var a i)), ToJSONKey (Var a i), FromJSONKey (Var a i), ToJSON (Rep i)) => ToJSON (ArithmeticCircuit a i o) where
    toJSON r = object
        [
            "system" .= acSystem r,
            "range"  .= acRange r,
            "output" .= acOutput r
        ]

-- TODO: properly restore the witness generation function
instance (FromJSON a, FromJSON (o (Var a i)), ToJSONKey (Var a i), FromJSONKey (Var a i), Haskell.Ord (Rep i), FromJSON (Rep i)) => FromJSON (ArithmeticCircuit a i o) where
    parseJSON =
        withObject "ArithmeticCircuit" $ \v -> do
            acSystem   <- v .: "system"
            acRange    <- v .: "range"
            acOutput   <- v .: "output"
            let acWitness = empty
            pure ArithmeticCircuit{..}
