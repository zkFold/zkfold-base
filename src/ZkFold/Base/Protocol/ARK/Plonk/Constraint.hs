{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Plonk.Constraint where

import           Control.Monad                                (guard)
import           Data.Containers.ListUtils                    (nubOrd)
import           Data.List                                    (find, permutations, sort)
import           Data.Map                                     (Map, empty)
import           Data.Maybe                                   (mapMaybe)
import           GHC.IsList                                   (IsList (..))
import           Numeric.Natural                              (Natural)
import           Prelude                                      hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                              (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Poly, polynomial, variables)
import           ZkFold.Prelude                               (length, take, (!!))

data PlonkConstraint a = PlonkConstraint
    { qm :: a
    , ql :: a
    , qr :: a
    , qo :: a
    , qc :: a
    , x1 :: Natural
    , x2 :: Natural
    , x3 :: Natural
    }
    deriving (Show, Eq)

instance (Arbitrary a, Finite a, ToConstant a Natural) => Arbitrary (PlonkConstraint a) where
    arbitrary = do
        qm <- arbitrary
        ql <- arbitrary
        qr <- arbitrary
        qo <- arbitrary
        qc <- arbitrary
        x1 <- toConstant <$> arbitrary @a
        x2 <- toConstant <$> arbitrary @a
        x3 <- toConstant <$> arbitrary @a
        let xs = sort [x1, x2, x3]
        return $ PlonkConstraint qm ql qr qo qc (xs !! 0) (xs !! 1) (xs !! 2)

toPlonkConstraint :: forall a . (Eq a, FiniteField a) => Poly a Natural Natural -> PlonkConstraint a
toPlonkConstraint p =
    let xs    = toList $ variables p
        i     = zero
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0 -> [i, i, i]
            1 -> [i, i, head xs, head xs]
            2 -> [i] ++ xs ++ xs
            _ -> xs ++ xs

        getCoef :: Map Natural Natural -> a
        getCoef m = case find (\(_, as) -> m == as) (toList p) of
            Just (c, _) -> c
            _           -> zero

        getCoefs :: [Natural] -> Maybe (PlonkConstraint a)
        getCoefs [a, b, c] = do
            let xa = [(a, 1)]
                xb = [(b, 1)]
                xc = [(c, 1)]
                xaxb = [(a, 1), (b, 1)]

                qm = getCoef $ fromList xaxb
                ql = getCoef $ fromList xa
                qr = getCoef $ fromList xb
                qo = getCoef $ fromList xc
                qc = getCoef $ empty
            guard $ p - polynomial [(qm, fromList xaxb), (ql, fromList xa), (qr, fromList xb), (qo, fromList xc), (qc, one)] == zero
            return $ PlonkConstraint qm ql qr qo qc a b c
        getCoefs _ = Nothing

    in head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (Eq a, Field a) => PlonkConstraint a -> Poly a Natural Natural
fromPlonkConstraint (PlonkConstraint qm ql qr qo qc a b c) =
    let xa = [(a, 1)]
        xb = [(b, 1)]
        xc = [(c, 1)]
        xaxb = [(a, 1), (b, 1)]

    in polynomial [(qm, xaxb), (ql, xa), (qr, xb), (qo, xc), (qc, one)]
