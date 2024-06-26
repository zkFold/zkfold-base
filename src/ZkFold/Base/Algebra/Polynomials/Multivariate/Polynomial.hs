{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications             #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial where

import           Control.DeepSeq                                       (NFData)
import           Data.Aeson                                            (FromJSON, ToJSON)
import           Data.Bifunctor                                        (Bifunctor (..))
import           Data.Bool                                             (bool)
import           Data.Functor                                          ((<&>))
import           Data.List                                             (foldl', intercalate)
import           Data.Map.Strict                                       (Map, empty)
import           Data.Set                                              (Set, singleton)
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
newtype Poly c i j = P [(c, Mono i j)]
    deriving (Generic, NFData, FromJSON, ToJSON)

---------------------------------- List-based polynomials with map-based monomials ----------------------------------

-- | Polynomial constructor
polynomial :: Polynomial c i j => [(c, Mono i j)] -> Poly c i j
polynomial = foldr (\(c, m) x -> if c == zero then x else P [(c, m)] + x) zero

evalPolynomial :: forall c i j b .
    Algebra c b =>
    ((i -> b) -> Mono i j -> b) -> (i -> b) -> Poly c i j -> b
evalPolynomial e f (P p) = foldr (\(c, m) x -> x + scale c (e f m)) zero p

variables :: forall c .
    MultiplicativeMonoid c =>
    Poly c Natural Natural -> Set Natural
variables = runSources . evalPolynomial evalMonomial (Sources @c . singleton)

mapVarPolynomial :: Variable i => Map i i-> Poly c i j -> Poly c i j
mapVarPolynomial m (P ms) = P $ second (mapVarMonomial m) <$> ms

mapCoeffs :: forall c c' i j .
    (c -> c')
    -> Poly c i j
    -> Poly c' i j
mapCoeffs f (P p) = P $ p <&> first f

instance Polynomial c i j => IsList (Poly c i j) where
    type Item (Poly c i j) = (c, Map i j)
    toList (P p) = second (\(M m) -> m) <$> p
    fromList p = polynomial $ second monomial <$> p

instance (Show c, Show i, Show j, Monomial i j) => Show (Poly c i j) where
    show (P p) = intercalate " + "
        $ p <&> \(c, m) -> show c <> "∙" <> show (m :: Mono i j)

instance Polynomial c i j => Eq (Poly c i j) where
    P l == P r = l == r

-- TODO: this assumes sorted monomials! Needs fixing.
instance Polynomial c i j => Ord (Poly c i j) where
    compare (P l) (P r) = compare
        (snd <$> l)
        (snd <$> r)

instance (Arbitrary c, Arbitrary (Mono i j)) => Arbitrary (Poly c i j) where
    arbitrary = P <$> arbitrary

instance Polynomial c i j => AdditiveSemigroup (Poly c i j) where
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

instance Scale c' c => Scale c' (Poly c i j) where
    scale c' (P p) = P $ map (first (scale c')) p

instance Polynomial c i j => AdditiveMonoid (Poly c i j) where
    zero = P []

instance Polynomial c i j => AdditiveGroup (Poly c i j) where
    negate (P p) = P $ map (first negate) p

instance Polynomial c i j => MultiplicativeSemigroup (Poly c i j) where
    P l * r = foldl' (+) (P []) $ map (f r) l
        where f (P p) (c, m) = P $ map (bimap (* c) (* m)) p

instance Polynomial c i j => Exponent (Poly c i j) Natural where
    (^) = natPow

instance Polynomial c i j => MultiplicativeMonoid (Poly c i j) where
    one = P [(one, M empty)]

instance FromConstant c' c => FromConstant c' (Poly c i j) where
    fromConstant x = P [(fromConstant x, M empty)]

instance Polynomial c i j => Semiring (Poly c i j)

instance Polynomial c i j => Ring (Poly c i j)

-- | @'var' i@ is a polynomial \(p(x) = x_i\)
var :: Polynomial c i j => i -> Poly c i j
var x = polynomial [(one, monomial $ fromList [(x, one)])]

lt :: Poly c i j -> Mono i j
lt (P [])         = M empty
lt (P ((_, m):_)) = m

zeroP :: Poly c i j -> Bool
zeroP (P []) = True
zeroP _      = False

reducable :: Polynomial c i j  => Poly c i j -> Poly c i j -> Bool
reducable l r = dividable (lt l) (lt r)

reduce ::
    forall c i j . (Ring j, Polynomial c i j)
    => Poly c i j
    -> Poly c i j
    -> Poly c i j
reduce l r =
    let q = P [(one, lt l / lt r)]
    in l - q * r

reduceMany ::
       forall c i j . (Ring j, Polynomial c i j)
    => Poly c i j
    -> [Poly c i j]
    -> Poly c i j
reduceMany h fs = if reduced then reduceMany h' fs else h'
  where
    (h', reduced) = reduceStep h fs False
    reduceStep p (q:qs) r
      | zeroP p   = (h, r)
      | otherwise =
        if reducable p q
          then (reduce p q, True)
          else reduceStep p qs r
    reduceStep p [] r = (p, r)

fullReduceMany ::
       forall c i j . (Ring j, Polynomial c i j)
    => Poly c i j
    -> [Poly c i j]
    -> Poly c i j
fullReduceMany h fs =
    let h' = reduceMany h fs
    in case h' of
        P []         -> h'
        P ((c, m):_) -> P [(c, m)] + fullReduceMany (h' - P [(c, m)]) fs

systemReduce ::
       forall c i j . (Ring j, Polynomial c i j)
    => [Poly c i j]
    -> [Poly c i j]
systemReduce = foldr f []
    where
        f p ps =
            let p' = fullReduceMany p ps
            in bool ps (p' : ps) (not $ zeroP p')
