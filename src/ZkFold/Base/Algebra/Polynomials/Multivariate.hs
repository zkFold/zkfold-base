{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate
    ( module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
    , module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
    , module ZkFold.Base.Algebra.Polynomials.Multivariate.Set
    , module ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution
    , Monomial'
    , Polynomial'
    , mapCoeffs
    , monomial
    , polynomial
    , evalPolynomial
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
import           Data.Map.Strict                                           (Map, keys, mapKeys, singleton, toList, delete)
import           Data.Maybe                                                (fromJust)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Num (..), length, product, replicate,
                                                                            sum, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Set
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution
import           ZkFold.Prelude                                            (elemIndex)

-- | Most general type for a multivariate monomial
type Monomial' = M Natural Natural (Map Natural Natural)

-- | Most general type for a multivariate polynomial
type Polynomial' c = P c Natural Natural (Map Natural Natural) [(c, Monomial')]

-- | Monomial constructor
monomial :: Monomial i j => Map i j -> M i j (Map i j)
monomial = M . fromJust . toMonomial

-- | Polynomial constructor
polynomial ::
    Polynomial c i j =>
    [(c, M i j (Map i j))] ->
    P c i j (Map i j) [(c, M i j (Map i j))]
polynomial = sum . map (\m -> P [m]) . toPolynomial

-- | @'var' i@ is a polynomial \(p(x) = x_i\)
var :: Polynomial c i j => i -> P c i j (Map i j) [(c, M i j (Map i j))]
var x = polynomial [(one, monomial (singleton x one))]

evalMonomial :: forall i j m b .
    FromMonomial i j m =>
    MultiplicativeMonoid b =>
    Exponent b j =>
    (i -> b) -> M i j m -> b
evalMonomial f (M m) = product
    $ toList (fromMonomial @i @j m)
        <&> (\(i, j) -> f i ^ j)

evalPolynomial :: forall p c i j m b .
    FromMonomial i j m =>
    FromPolynomial c i j m p =>
    Algebra c b =>
    Exponent b j =>
    (i -> b) -> P c i j m p -> b
evalPolynomial f (P p) = sum
    $ fromPolynomial @c @i @j @m @p p
        <&> (\(c, m) -> scale c $ evalMonomial f m)

variables :: forall c i j m p .
    FromMonomial i j m =>
    FromPolynomial c i j m p =>
    P c i j m p -> [i]
variables (P p) = nubOrd
    . concatMap (\(_, M m) -> keys (fromMonomial @i @j @m m))
    $ fromPolynomial @c @i @j @m @p p

mapCoeffs :: forall c c' i j m p p' .
    FromPolynomial c i j m p =>
    ToPolynomial c' i j m p' =>
    (c -> c') -> P c i j m p -> P c' i j m p'
mapCoeffs f (P p) = P . toPolynomial
    $ fromPolynomial @c @i @j @m p
        <&> first f

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
