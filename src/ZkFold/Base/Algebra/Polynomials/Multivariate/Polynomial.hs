{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
    ( P(..)
    , Polynomial
    , FromPolynomial(..)
    , ToPolynomial(..)
    ) where

import           Control.DeepSeq                                       (NFData)
import           Data.Aeson                                            (FromJSON, ToJSON)
import           Data.Bifunctor                                        (Bifunctor (..))
import           Data.Functor                                          ((<&>))
import           Data.List                                             (foldl', intercalate)
import           Data.Map.Strict                                       (Map, empty)
import           GHC.Generics                                          (Generic)
import           Numeric.Natural                                       (Natural)
import           Prelude                                               hiding (Num (..), drop, lcm, length, sum, take,
                                                                        (!!), (/))
import           Test.QuickCheck                                       (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial

-- | A class for polynomials.
-- `c` is the coefficient type,
-- `i` is the variable type,
-- `j` is the power type.
type Polynomial c i j = (Eq c, Field c, Monomial i j)

class Polynomial c i j => FromPolynomial c i j m p where
    fromPolynomial :: p -> [(c, M i j m)]

instance Polynomial c i j => FromPolynomial c i j m [(c, M i j m)] where
    fromPolynomial = id

class Polynomial c i j => ToPolynomial c i j m p where
    toPolynomial   :: [(c, M i j m)] -> Maybe p

instance (Polynomial c i j) => ToPolynomial c i j m [(c, M i j m)] where
    toPolynomial   = Just . filter (\(c, _) -> c /= zero)

-- | Polynomial type
newtype P c i j m p = P p
    deriving (Generic, NFData, FromJSON, ToJSON)

instance (Show c, Show i, Show j, FromPolynomial c i j m p, FromMonomial i j m) => Show (P c i j m p) where
    show (P p) = intercalate " + "
        $ fromPolynomial @c @i @j p
            <&> \(c, m) -> show c <> "∙" <> show (m :: M i j m)

instance (FromPolynomial c i j m p, FromMonomial i j m) => Eq (P c i j m p) where
    (P l) == (P r) = fromPolynomial @c @i @j @m l == fromPolynomial r

-- TODO: this assumes sorted monomials! Needs fixing.
instance (FromPolynomial c i j m p, FromMonomial i j m) => Ord (P c i j m p) where
    compare (P l) (P r) = compare (map snd $ fromPolynomial @c @i @j @m l) (map snd $ fromPolynomial @c @i @j @m r)

instance Arbitrary p => Arbitrary (P c i j m p) where
    arbitrary = P <$> arbitrary

{-
    In general, `P c i j m p` may define a set of polynomials that is not necessarily a ring.
    Arithmetic operations are defined for a more concrete type below.
-}

instance (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => AdditiveSemigroup (P c i j m p) where
    P l + P r = P $ go l r
        where
            go :: [(c, M i j m)] -> [(c, M i j m)] -> [(c, M i j m)]
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

instance (Scale c' c, m ~ Map i j, p ~ [(c, M i j m)]) => Scale c' (P c i j m p) where
    scale c' (P p) = P $ map (first (scale c')) p

instance forall c i j m p . (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => AdditiveMonoid (P c i j m p) where
    zero = P []

instance (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => AdditiveGroup (P c i j m p) where
    negate (P p) = P $ map (first negate) p

instance (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => MultiplicativeSemigroup (P c i j m p) where
    P l * r = foldl' (+) (P []) $ map (f r) l
        where f (P p) (c, m) = P $ map (bimap (* c) (* m)) p

instance MultiplicativeMonoid (P c i j m p) => Exponent (P c i j m p) Natural where
    (^) = natPow

instance forall c i j m p . (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => MultiplicativeMonoid (P c i j m p) where
    one = P [(one, M empty)]

instance (FromConstant c' c, m ~ Map i j, p ~ [(c, M i j m)]) => FromConstant c' (P c i j m p) where
    fromConstant x = P [(fromConstant x, M empty)]

instance (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => Semiring (P c i j m p)

instance forall c i j m p . (Polynomial c i j, m ~ Map i j, p ~ [(c, M i j m)]) => Ring (P c i j m p)
