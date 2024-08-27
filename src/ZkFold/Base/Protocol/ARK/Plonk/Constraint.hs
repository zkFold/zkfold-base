{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Plonk.Constraint where

import           Control.Monad                                       (guard)
import           Data.Containers.ListUtils                           (nubOrd)
import           Data.List                                           (find, permutations, sort)
import           Data.Map                                            (Map, empty, fromListWith)
import           Data.Maybe                                          (mapMaybe)
import           GHC.IsList                                          (IsList (..))
import           GHC.TypeNats                                        (KnownNat)
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (Poly, polynomial, var, variables)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Prelude                                      (length, take, (!!))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkConstraint i a = PlonkConstraint
    { qm :: a
    , ql :: a
    , qr :: a
    , qo :: a
    , qc :: a
    , x1 :: Var (Vector i)
    , x2 :: Var (Vector i)
    , x3 :: Var (Vector i)
    }
    deriving (Show, Eq)

instance (Arbitrary a, Finite a, ToConstant a Natural, KnownNat i) => Arbitrary (PlonkConstraint i a) where
    arbitrary = do
        qm <- arbitrary
        ql <- arbitrary
        qr <- arbitrary
        qo <- arbitrary
        qc <- arbitrary
        x1 <- NewVar . toConstant @a <$> arbitrary
        x2 <- NewVar . toConstant @a <$> arbitrary
        x3 <- NewVar . toConstant @a <$> arbitrary
        let xs = sort [x1, x2, x3]
        return $ PlonkConstraint qm ql qr qo qc (xs !! 0) (xs !! 1) (xs !! 2)

toPlonkConstraint :: forall a i . (Eq a, FiniteField a, KnownNat i) => Poly a (Var (Vector i)) Natural -> PlonkConstraint i a
toPlonkConstraint p =
    let xs    = toList $ variables p
        i     = NewVar zero
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0 -> [i, i, i]
            1 -> [i, i, head xs, head xs]
            2 -> [i] ++ xs ++ xs
            _ -> xs ++ xs

        getCoef :: Map (Var (Vector i)) Natural -> a
        getCoef m = case find (\(_, as) -> m == as) (toList p) of
            Just (c, _) -> c
            _           -> zero

        getCoefs :: [Var (Vector i)] -> Maybe (PlonkConstraint i a)
        getCoefs [a, b, c] = do
            let xa = [(a, 1)]
                xb = [(b, 1)]
                xc = [(c, 1)]
                xaxb = [(a, 1), (b, 1)]

                qm = getCoef $ fromListWith (+) xaxb
                ql = getCoef $ fromList xa
                qr = getCoef $ fromList xb
                qo = getCoef $ fromList xc
                qc = getCoef $ empty
            guard $ p - polynomial [(qm, fromList xaxb), (ql, fromList xa), (qr, fromList xb), (qo, fromList xc), (qc, one)] == zero
            return $ PlonkConstraint qm ql qr qo qc a b c
        getCoefs _ = Nothing

    in head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (Eq a, Scale a a, FromConstant a a, Field a, KnownNat i) => PlonkConstraint i a -> Poly a (Var (Vector i)) Natural
fromPlonkConstraint (PlonkConstraint qm ql qr qo qc a b c) =
    let xvar v = if v == NewVar zero then zero else var v
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
