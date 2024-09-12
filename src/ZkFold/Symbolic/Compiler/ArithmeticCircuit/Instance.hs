{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans     #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance where

import           Data.Aeson                                          hiding (Bool)
import           Data.Functor.Rep                                    (Representable (..))
import           Data.Map                                            hiding (drop, foldl, foldl', foldr, map, null,
                                                                      splitAt, take, toList)
import           Data.Type.Equality                                  (type (~))
import           GHC.Generics                                        (Par1 (..))
import           Prelude                                             (Show, mempty, pure, return, show, ($), (++),
                                                                      (<$>), mapM, fmap, const, id)
import qualified Prelude                                             as Haskell
import           System.Random                                       (mkStdGen)
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen, elements)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Package                            (packWith)
import           ZkFold.Base.Data.Par1                               ()
import           ZkFold.Base.Data.Vector                             (Vector, generate)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal hiding (constraint)
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement (..))

------------------------------------- Instances -------------------------------------

instance
  ( Arithmetic a
  , Arbitrary a
  , Arbitrary (Rep i)
  , Haskell.Ord (Rep i)
  , Representable i
  , Haskell.Foldable i
  , ToConstant (Rep i)
  , Const (Rep i) ~ Natural
  ) => Arbitrary (ArithmeticCircuit a i Par1) where
    arbitrary = do
        outVar <- InVar <$> arbitrary
        let ac = mempty {acOutput = Par1 outVar}
        fromFieldElement <$> arbitrary' (FieldElement ac) 10

instance
  ( Arithmetic a
  , Arbitrary a
  , Arbitrary (Rep i)
  , Haskell.Ord (Rep i)
  , Representable i
  , Haskell.Foldable i
  , ToConstant (Rep i)
  , Const (Rep i) ~ Natural
  , KnownNat l
  ) => Arbitrary (ArithmeticCircuit a i (Vector l)) where
    arbitrary = packWith (fmap unPar1) <$> mapM (const arbitrary) (generate @l id)

arbitrary' ::
  forall a i .
  (Arithmetic a, Arbitrary a) =>
  (Haskell.Ord (Rep i), Representable i, Haskell.Foldable i) =>
  (ToConstant (Rep i), Const (Rep i) ~ Natural) =>
  FieldElement (ArithmeticCircuit a i) -> Natural ->
  Gen (FieldElement (ArithmeticCircuit a i))
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
instance (FiniteField a, Haskell.Eq a, Show a, Show (o (Var i)), Haskell.Ord (Rep i), Show (Var i)) => Show (ArithmeticCircuit a i o) where
    show r = "ArithmeticCircuit { acSystem = " ++ show (acSystem r)
                          ++ "\n, acRange = " ++ show (acRange r)
                          ++ "\n, acOutput = " ++ show (acOutput r)
                          ++ " }"

-- TODO: add witness generation info to the JSON object
instance (ToJSON a, ToJSON (o (Var i)), ToJSONKey (Var i), FromJSONKey (Var i)) => ToJSON (ArithmeticCircuit a i o) where
    toJSON r = object
        [
            "system" .= acSystem r,
            "range"  .= acRange r,
            "output" .= acOutput r
        ]

-- TODO: properly restore the witness generation function
instance (FromJSON a, FromJSON (o (Var i)), ToJSONKey (Var i), FromJSONKey (Var i), Haskell.Ord (Rep i)) => FromJSON (ArithmeticCircuit a i o) where
    parseJSON =
        withObject "ArithmeticCircuit" $ \v -> do
            acSystem   <- v .: "system"
            acRange    <- v .: "range"
            acOutput   <- v .: "output"
            let acWitness = empty
                acRNG     = mkStdGen 0
            pure ArithmeticCircuit{..}
