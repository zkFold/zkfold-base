{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.PlonkConstraint where

import           Control.Monad                                       (guard, return)
import           Data.Binary                                         (Binary, encode)
import           Data.ByteString                                     (toStrict)
import           Data.Containers.ListUtils                           (nubOrd)
import           Data.Eq                                             (Eq (..))
import           Data.Function                                       (($), (.))
import           Data.Functor                                        ((<$>))
import           Data.List                                           (find, head, map, permutations, sort, (++))
import           Data.Map                                            (Map)
import qualified Data.Map                                            as Map
import           Data.Maybe                                          (Maybe (..), mapMaybe, maybe)
import           GHC.IsList                                          (IsList (..))
import           GHC.TypeNats                                        (KnownNat)
import           Numeric.Natural                                     (Natural)
import           Prelude                                             (error)
import           Test.QuickCheck                                     (Arbitrary (..), elements)
import           Text.Show                                           (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (Poly, evalMonomial, evalPolynomial, polynomial,
                                                                      var, variables)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Prelude                                      (length, replicate, replicateA, take)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkConstraint i a = PlonkConstraint
    { qm :: a
    , ql :: a
    , qr :: a
    , qo :: a
    , qc :: a
    , x1 :: Maybe (Var (Vector i))
    , x2 :: Maybe (Var (Vector i))
    , x3 :: Maybe (Var (Vector i))
    }
    deriving (Show, Eq)

instance (Arbitrary a, Binary a, KnownNat i) => Arbitrary (PlonkConstraint i a) where
    arbitrary = do
        qm <- arbitrary
        ql <- arbitrary
        qr <- arbitrary
        qo <- arbitrary
        qc <- arbitrary
        k <- elements [1, 2, 3]
        xs0 <- sort <$> replicateA k (Just . NewVar . toStrict . encode @a <$> arbitrary)
        let (x, y, z) = case replicate (3 -! k) Nothing ++ xs0 of
              [x', y', z'] -> (x', y', z')
              _            -> error "impossible"
        return $ PlonkConstraint qm ql qr qo qc x y z

toPlonkConstraint :: forall a i . (Eq a, FiniteField a, KnownNat i) => Poly a (Var (Vector i)) Natural -> PlonkConstraint i a
toPlonkConstraint p =
    let xs    = map Just $ toList (variables p)
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0 -> [Nothing, Nothing, Nothing]
            1 -> [Nothing, Nothing, head xs, head xs]
            2 -> [Nothing] ++ xs ++ xs
            _ -> xs ++ xs

        getCoef :: Map (Maybe (Var (Vector i))) Natural -> a
        getCoef m = case find (\(_, as) -> m == Map.mapKeys Just as) (toList p) of
            Just (c, _) -> c
            _           -> zero

        getCoefs :: [Maybe (Var (Vector i))] -> Maybe (PlonkConstraint i a)
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
            return $ PlonkConstraint qm ql qr qo qc a b c
        getCoefs _ = Nothing

    in head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (Eq a, Field a, KnownNat i) => PlonkConstraint i a -> Poly a (Var (Vector i)) Natural
fromPlonkConstraint (PlonkConstraint qm ql qr qo qc a b c) =
    let xvar = maybe zero var
        xa = xvar a
        xb = xvar b
        xc = xvar c
        xaxb = xa * xb
    in
              scale qm xaxb
            + scale ql xa
            + scale qr xb
            + scale qo xc
            + fromConstant qc
