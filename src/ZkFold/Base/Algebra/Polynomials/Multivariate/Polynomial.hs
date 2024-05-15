{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
    ( Polynomial
    , Polynomial'
    , polynomial
    , PolynomialAny
    , PolynomialRepAny
    , PolynomialBoundedDegree
    , PolynomialRepBoundedDegree
    , mapCoeffs
    , var
    , evalPolynomial
    , mapVarPolynomial
    , variables
    ) where

import           Control.DeepSeq                                       (NFData)
import           Data.Aeson                                            (FromJSON, ToJSON)
import           Data.Bifunctor                                        (Bifunctor (..))
import           Data.Functor                                          ((<&>))
import           Data.List                                             (foldl', intercalate)
import           Data.Set                                              (Set, singleton)
import           Data.Map.Strict                                       (Map, empty)
import           GHC.Generics                                          (Generic)
import           GHC.IsList                                            (IsList (..))
import           Numeric.Natural                                       (Natural)
import           Prelude                                               hiding (Num (..), drop, lcm, length, sum, take,
                                                                        (!!), (/))
import           Test.QuickCheck                                       (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Sources
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial

-- | A class for polynomials.
-- `c` is the coefficient type,
-- `i` is the variable type,
-- `j` is the power type.
type Polynomial c i j = (Eq c, Field c, Monomial i j)

-- | Polynomial type
newtype P c i j m p = P p
    deriving (Generic, NFData, FromJSON, ToJSON)

-- | Most general type for a multivariate polynomial
type Polynomial' c = P c Natural Natural (Map Natural Natural) [(c, Monomial')]

type PolynomialRepAny c = [(c, MonomialAny)]

type PolynomialRepBoundedDegree c i d = [(c, MonomialBoundedDegree i d)]

-- | Most general type for a multivariate polynomial, parameterized by the field of coefficients
type PolynomialAny c = P c Integer Integer MonomialRepAny (PolynomialRepAny c)

-- | Most general type for a multivariate polynomial with bounded degree,
-- parameterized by the field of coefficients, the type of variables, and the degree
type PolynomialBoundedDegree c i d = P c i Bool (MonomialRepBoundedDegree i d) (PolynomialRepBoundedDegree c i d)

-- | Polynomial constructor
polynomial ::
    Polynomial c i j =>
    [(c, M i j (Map i j))] ->
    P c i j (Map i j) [(c, M i j (Map i j))]
polynomial = foldr (\(c, m) x -> if c == zero then x else P [(c, m)] + x) zero

instance (Ord i, Eq c, Field c, Ord j, Semiring j) => IsList (P c i j (Map i j) [(c, M i j (Map i j))]) where
    type Item (P c i j (Map i j) [(c, M i j (Map i j))]) = (c, Map i j)
    toList (P p) = second (\(M m) -> m) <$> p
    fromList p = polynomial $ second monomial <$> p

instance (Show c, Show i, Show j, Monomial i j) => Show (P c i j (Map i j) [(c, M i j (Map i j))]) where
    show (P p) = intercalate " + "
        $ p <&> \(c, m) -> show c <> "∙" <> show (m :: M i j (Map i j))

instance (Eq i, Eq j, Eq c, Eq (Map i j)) => Eq (P c i j m [(c, M i j (Map i j))]) where
    P l == P r = l == r

-- TODO: this assumes sorted monomials! Needs fixing.
instance (Eq i, Eq j, Eq c, Ord (M i j (Map i j))) => Ord (P c i j m [(c, M i j (Map i j))]) where
    compare (P l) (P r) = compare
        (snd <$> l)
        (snd <$> r)

instance (Arbitrary c, Arbitrary m) => Arbitrary (P c i j m [(c, M i j m)]) where
    arbitrary = P <$> arbitrary

{-
    In general, `P c i j m p` may define a set of polynomials that is not necessarily a ring.
    Arithmetic operations are defined for a more concrete type below.
-}

instance Polynomial c i j => AdditiveSemigroup (P c i j (Map i j) [(c, M i j (Map i j))]) where
    P l + P r = P $ go l r
        where
            go [] [] = []
            go ls [] = ls
            go [] rs = rs
            go ((cl, ml):ls) ((cr, mr):rs)
                | ml == mr =
                    if cl + cr == zero
                        then go ls rs
                        else (cl + cr, ml) : go ls rs
                | ml > mr   = (cl, ml) : go ls ((cr, mr):rs)
                | otherwise = (cr, mr) : go ((cl, ml):ls) rs

instance Scale c' c => Scale c' (P c i j (Map i j) [(c, M i j (Map i j))]) where
    scale c' (P p) = P $ map (first (scale c')) p

instance Polynomial c i j => AdditiveMonoid (P c i j (Map i j) [(c, M i j (Map i j))]) where
    zero = P []

instance Polynomial c i j => AdditiveGroup (P c i j (Map i j) [(c, M i j (Map i j))]) where
    negate (P p) = P $ map (first negate) p

instance Polynomial c i j => MultiplicativeSemigroup (P c i j (Map i j) [(c, M i j (Map i j))]) where
    P l * r = foldl' (+) (P []) $ map (f r) l
        where f (P p) (c, m) = P $ map (bimap (* c) (* m)) p

instance Polynomial c i j => Exponent (P c i j (Map i j) [(c, M i j (Map i j))]) Natural where
    (^) = natPow

instance Polynomial c i j => MultiplicativeMonoid (P c i j (Map i j) [(c, M i j (Map i j))]) where
    one = P [(one, M empty)]

instance FromConstant c' c => FromConstant c' (P c i j (Map i j) [(c, M i j (Map i j))]) where
    fromConstant x = P [(fromConstant x, M empty)]

instance Polynomial c i j => Semiring (P c i j (Map i j) [(c, M i j (Map i j))])

instance Polynomial c i j => Ring (P c i j (Map i j) [(c, M i j (Map i j))])

-- | @'var' i@ is a polynomial \(p(x) = x_i\)
var :: Polynomial c i j => i -> P c i j (Map i j) [(c, M i j (Map i j))]
var x = polynomial [(one, monomial $ fromList [(x, one)])]

evalPolynomial :: forall c i j b m .
    Algebra c b =>
    ((i -> b) -> M i j m -> b) -> (i -> b) -> P c i j m [(c, M i j m)] -> b
evalPolynomial e f (P p) = foldr (\(c, m) x -> x + scale c (e f m)) zero p

variables :: forall c .
    MultiplicativeMonoid c =>
    Polynomial' c -> Set Natural
variables = runSources . evalPolynomial evalMapM (Sources @c . singleton)

mapCoeffs :: forall c c' i j .
    (c -> c')
    -> P c i j (Map i j) [(c, M i j (Map i j))]
    -> P c' i j (Map i j) [(c', M i j (Map i j))]
mapCoeffs f (P p) = P $ p <&> first f

mapVarPolynomial :: [Natural] -> Polynomial' c -> Polynomial' c
mapVarPolynomial vars (P ms) = P $ second (mapVarMonomial vars) <$> ms
