{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.PlonkConstraint where

import           Control.Monad                                       (guard, replicateM, return)
import           Data.Binary                                         (Binary)
import           Data.Containers.ListUtils                           (nubOrd)
import           Data.Eq                                             (Eq (..))
import           Data.Function                                       (($), (.))
import           Data.Functor                                        ((<$>))
import           Data.Functor.Rep                                    (Rep)
import           Data.List                                           (find, head, map, permutations, sort, (!!), (++))
import           Data.Map                                            (Map)
import qualified Data.Map                                            as Map
import           Data.Maybe                                          (Maybe (..), fromMaybe, mapMaybe)
import           Data.Ord                                            (Ord)
import           GHC.IsList                                          (IsList (..))
import           Numeric.Natural                                     (Natural)
import           Test.QuickCheck                                     (Arbitrary (..))
import           Text.Show                                           (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (Poly, evalMonomial, evalPolynomial, polynomial,
                                                                      var, variables)
import           ZkFold.Base.Data.ByteString                         (toByteString)
import           ZkFold.Prelude                                      (length, take)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Var      (toVar)

data PlonkConstraint i a = PlonkConstraint
    { qm :: a
    , ql :: a
    , qr :: a
    , qo :: a
    , qc :: a
    , x1 :: Var a i
    , x2 :: Var a i
    , x3 :: Var a i
    }

deriving instance (Show a, Show (Rep i)) => Show (PlonkConstraint i a)
deriving instance (Eq a, Eq (Rep i)) => Eq (PlonkConstraint i a)

instance (Ord a, Arbitrary a, Binary a, Ord (Rep i), Semiring a) => Arbitrary (PlonkConstraint i a) where
    arbitrary = do
        qm <- arbitrary
        ql <- arbitrary
        qr <- arbitrary
        qo <- arbitrary
        qc <- arbitrary
        let arbitraryNewVar = toVar . NewVar . EqVar . toByteString @a <$> arbitrary
        xs <- sort <$> replicateM 3 arbitraryNewVar
        let x1 = head xs; x2 = xs !! 1; x3 = xs !! 2
        return $ PlonkConstraint qm ql qr qo qc x1 x2 x3

toPlonkConstraint :: forall a i . (Ord a, FiniteField a, Ord (Rep i)) => Poly a (Var a i) Natural -> PlonkConstraint i a
toPlonkConstraint p =
    let xs    = Just <$> toList (variables p)
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0 -> [Nothing, Nothing, Nothing]
            1 -> [Nothing, Nothing, head xs, head xs]
            2 -> [Nothing] ++ xs ++ xs
            _ -> xs ++ xs

        getCoef :: Map (Maybe (Var a i)) Natural -> a
        getCoef m = case find (\(_, as) -> m == Map.mapKeys Just as) (toList p) of
            Just (c, _) -> c
            _           -> zero

        getCoefs :: [Maybe (Var a i)] -> Maybe (PlonkConstraint i a)
        getCoefs [a, b, c] = do
            let xa = [(a, 1)]
                xb = [(b, 1)]
                xc = [(c, 1)]
                xaxb = xa ++ xb

                qm = getCoef $ Map.fromListWith (+) xaxb
                ql = getCoef $ fromList xa
                qr = getCoef $ fromList xb
                qo = getCoef $ fromList xc
                qc = getCoef Map.empty
            guard $ evalPolynomial evalMonomial (var . Just) p - polynomial [(qm, fromList xaxb), (ql, fromList xa), (qr, fromList xb), (qo, fromList xc), (qc, one)] == zero
            let va = fromMaybe (ConstVar one) a
                vb = fromMaybe (ConstVar one) b
                vc = fromMaybe (ConstVar one) c
            return $ PlonkConstraint qm ql qr qo qc va vb vc
        getCoefs _ = Nothing

    in case mapMaybe getCoefs perms of
        [] -> toPlonkConstraint zero
        _  -> head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (Ord a, Field a, Ord (Rep i)) => PlonkConstraint i a -> Poly a (Var a i) Natural
fromPlonkConstraint (PlonkConstraint qm ql qr qo qc a b c) =
    let xa = var a
        xb = var b
        xc = var c
        xaxb = xa * xb
    in
              scale qm xaxb
            + scale ql xa
            + scale qr xb
            + scale qo xc
            + fromConstant qc
