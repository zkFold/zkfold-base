{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate
    ( module ZkFold.Base.Algebra.Polynomials.Multivariate.Set
    , module ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution
    , Monomial
    -- , ToMonomial(..)
    , Variable
    , Polynomial
    , Monomial'
    , Polynomial'
    , mapCoeffs
    , monomial
    , polynomial
    , evalMapPolynomial
    , evalVectorPolynomial
    , var
    , variables
    , mapVar
    , mapVarMonomial
    , mapVarPolynomial
    , mapVarPolynomials
    , removeConstantVariable
    ) where

import           Data.Bifunctor                                            (first, second)
import           Data.Containers.ListUtils                                 (nubOrd)
import           Data.Functor                                              ((<&>))
import           Data.List                                                 (filter)
import           Data.Map.Strict                                           (Map, delete, filter, fromListWith, keys,
                                                                            mapKeys, singleton, toList)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Num (..), length, product, replicate,
                                                                            sum, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Set
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution
import           ZkFold.Base.Data.Vector
import           ZkFold.Prelude                                            (elemIndex)

-- | Most general type for a multivariate monomial
type Monomial' = M Natural Natural (Map Natural Natural)

-- | Most general type for a multivariate polynomial
type Polynomial' c = P c Natural Natural (Map Natural Natural) [(c, Monomial')]

-- | Monomial constructor
monomial :: Monomial i j => Map i j -> M i j (Map i j)
monomial = M . Data.Map.Strict.filter (/= zero)

-- | Polynomial constructor
polynomial ::
    Polynomial c i j =>
    [(c, M i j (Map i j))] ->
    P c i j (Map i j) [(c, M i j (Map i j))]
polynomial = sum . map (\m -> P [m]) . Data.List.filter (\(c, _) -> c /= zero)

-- | @'var' i@ is a polynomial \(p(x) = x_i\)
var :: Polynomial c i j => i -> P c i j (Map i j) [(c, M i j (Map i j))]
var x = polynomial [(one, monomial (singleton x one))]

evalMapMonomial :: forall i j b .
    MultiplicativeMonoid b =>
    Exponent b j =>
    (i -> b) -> M i j (Map i j) -> b
evalMapMonomial f (M m) = product
    $ toList m <&> (\(i, j) -> f i ^ j)

evalVectorMonomial :: forall i j b d .
    Monomial i j =>
    MultiplicativeMonoid b =>
    Exponent b j =>
    (i -> b) -> M i j (Vector d (i, Bool)) -> b
evalVectorMonomial f (M v) = product $ toList (toM v) <&> (\(i, j) -> f i ^ j) where
    toM :: Vector d (i, Bool) -> Map i j
    toM v = fromListWith (+) $ map (\(i, _) -> (i, one)) $ Data.List.filter snd $ fromVector v

evalMapPolynomial :: forall c i j b .
    Algebra c b =>
    Exponent b j =>
    (i -> b) -> P c i j (Map i j) [(c, M i j (Map i j))] -> b
evalMapPolynomial f (P p) = sum
    $ p <&> (\(c, m) -> scale c $ evalMapMonomial f m)

evalVectorPolynomial :: forall c i j b d .
    Polynomial c i j =>
    Algebra c b =>
    Exponent b j =>
    (i -> b) -> P c i j (Vector d (i, Bool)) [(c, M i j (Vector d (i, Bool)))] -> b
evalVectorPolynomial f (P p) = sum
    $ p <&> (\(c, m) -> scale c $ evalVectorMonomial f m)

variables :: forall c i j .
    Ord i =>
    P c i j (Map i j) [(c, M i j (Map i j))] -> [i]
variables (P p) = nubOrd
    . concatMap (\(_, M m) -> keys m)
    $ p

mapCoeffs :: forall c c' i j .
    (c -> c')
    -> P c i j (Map i j) [(c, M i j (Map i j))]
    -> P c' i j (Map i j) [(c', M i j (Map i j))]
mapCoeffs f (P p) = P $ p <&> first f

mapVarMonomial :: [Natural] -> Monomial' -> Monomial'
mapVarMonomial vars (M as) = M $ mapKeys (mapVar vars) as

mapVar :: [Natural] -> Natural -> Natural
mapVar vars x = case x `elemIndex` vars of
    Just i  -> i
    Nothing -> error "mapVar: something went wrong"

mapVarPolynomial :: [Natural] -> Polynomial' c -> Polynomial' c
mapVarPolynomial vars (P ms) = P $ second (mapVarMonomial vars) <$> ms

mapVarPolynomials :: [Natural] -> [Polynomial' c] -> [Polynomial' c]
mapVarPolynomials vars = map (mapVarPolynomial vars)

removeConstantVariable :: (Eq c, Field c) => Polynomial' c -> Polynomial' c
removeConstantVariable (P ms) =
    polynomial . map (\(c, M as) -> (c, M (0 `delete` as))) $ ms
