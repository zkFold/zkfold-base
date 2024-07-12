{-# LANGUAGE
AllowAmbiguousTypes
, DerivingStrategies
, TypeOperators
, UndecidableInstances
, UndecidableSuperClasses
#-}

module ZkFold.Symbolic.Base.Polynomial
  ( Poly
  , Mono (..), mono
  , Combo (..), combo
  , var
  , varSet
  , evalPoly
  , mapPoly
  ) where

import Control.Category
import Data.Bifunctor
import Data.Eq
import Data.Ord
import Data.Either
import Data.Foldable hiding (toList, sum, product)
import Data.Functor
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Prelude
import GHC.IsList
import GHC.TypeNats

import ZkFold.Symbolic.Base.Num

newtype Mono var pow = UnsafeMono {fromMono :: Map var pow}
  deriving (Eq, Ord, Functor)

mono :: (AdditiveMonoid pow, Eq pow) => Map var pow -> Mono var pow
mono = UnsafeMono . Map.filter (/= zero)

instance (Ord var, AdditiveMonoid pow, Eq pow)
  => IsList (Mono var pow) where
    type Item (Mono var pow) = (var,pow)
    toList (UnsafeMono m) = toList m
    fromList l =
      let
        inserter m (v, pow) = Map.insertWith (+) v pow m
      in
        mono (foldl' inserter Map.empty l)

instance (Ord var, Semiring pow, Eq pow)
  => MultiplicativeMonoid (Mono var pow) where
    one = UnsafeMono Map.empty
    UnsafeMono x * UnsafeMono y = mono (Map.unionWith (+) x y)

instance (Ord var, Semiring pow, Ord pow)
  => Exponent Natural (Mono var pow) where
    exponent a p = evalMono [(a,p)]
    evalMono = evalMonoN

newtype Combo var coef = UnsafeCombo {fromCombo :: Map var coef}
  deriving (Eq, Ord, Functor)

combo :: (AdditiveMonoid coef, Eq coef) => Map var coef -> Combo var coef
combo = UnsafeCombo . Map.filter (/= zero)

instance (Ord var, Semiring coef, Eq coef)
  => AdditiveMonoid (Combo var coef) where
    zero = UnsafeCombo Map.empty
    UnsafeCombo x + UnsafeCombo y = combo (Map.unionWith (+) x y)

instance (Ord var, Ring coef, Eq coef)
  => AdditiveGroup (Combo var coef) where
    negate (UnsafeCombo x) = UnsafeCombo (Map.map negate x)
    UnsafeCombo x - UnsafeCombo y = combo (Map.unionWith (-) x y)

instance (Ord var, AdditiveMonoid coef, Eq coef)
  => IsList (Combo var coef) where
    type Item (Combo var coef) = (coef,var)
    toList (UnsafeCombo m) = [(c,v) | (v,c) <- toList m]
    fromList l =
      let
        inserter m (c,v) = Map.insertWith (+) v c m
      in
        combo (foldl' inserter Map.empty l)

type Poly var pow = Combo (Mono var pow)
instance (Ord var, Ord pow, Semiring pow, Semiring coef, Eq coef)
  => From coef (Poly var pow coef) where
    from coef = fromList [(coef,one)]
instance (Ord var, Ord pow, Semiring pow, Semiring coef, Eq coef)
  => From Natural (Poly var pow coef) where
    from = from @coef . from
instance (Ord var, Ord pow, Semiring pow, Ring coef, Eq coef)
  => From Integer (Poly var pow coef) where
    from = from @coef . from
instance (Ord var, Ord pow, Semiring pow, Field coef, Eq coef)
  => From Rational (Poly var pow coef) where
    from = from @coef . from
instance From (Poly var pow coef) (Poly var pow coef)
instance (Ord var, Ord pow, Semiring pow, Semiring coef, Eq coef)
  => MultiplicativeMonoid (Poly var pow coef) where
    one = fromList [(one, one)]
    x * y = fromList
      [ (xCoef * yCoef, xMono * yMono)
      | (xCoef, xMono) <- toList x
      , (yCoef, yMono) <- toList y
      ]
instance (Ord var, Ord pow, Semiring pow, Semiring coef, Ord coef)
  => Exponent Natural (Poly var pow coef) where
    exponent x p = evalMono [(x,p)]
    evalMono = evalMonoN
instance (Ord var, Ord pow, Semiring pow, Semiring x, Eq x)
  => Scalar x (Poly var pow x) where
    scale c = if c == zero then Prelude.const zero else fmap (c *)
    combine polys = product [scale c p | (c,p) <- polys]
    -- TODO: consider how to optimize combine
    -- using an additional Scalar x x constraint
    -- since then we can hopefully applicatively apply combine
    -- to monomials...
instance (Ord var, Ord pow, Semiring x, Eq x)
  => Scalar Natural (Poly var pow x) where
    scale c = if c == zero then Prelude.const zero else fmap (from c *)
    combine = combineN
instance (Ord var, Ord pow, Ring x, Eq x)
  => Scalar Integer (Poly var pow x) where
    scale c = if c == zero then Prelude.const zero else fmap (from c *)
    combine = combineZ
instance (Ord var, Ord pow, Semiring pow, Semiring x, Ord x)
  => Scalar (Poly var pow x) (Poly var pow x)

var
  :: (Ord var, Ord pow, Semiring pow, Semiring coef, Eq coef)
  => var -> Poly var pow coef
var x = fromList [(one, fromList [(x,one)])]

varSet :: Ord var => Poly var pow coef -> Set var
varSet
  = Set.unions
  . Set.map (Map.keysSet . fromMono)
  . Map.keysSet
  . fromCombo

-- evaluate a polynomial in its field of coefficients
evalPoly :: (Ord x, Semiring x) => Poly x Natural x -> x
evalPoly x = combine [(c, evalMono (toList m)) | (c,m) <- toList x]

-- map a polynomial to new variables and evaluate some variables
mapPoly
  :: (Eq x, Ord var0, Ord var1, Semiring x)
  => (var0 -> Either x var1)
  -> Poly var0 Natural x -> Poly var1 Natural x
mapPoly f varPoly = fromList
  [
    let
      (coefs, varList) = partitionEithers
        [bimap (^p) (,p) (f v0) | (v0,p) <- toList varMono]
    in
      (c * product coefs, fromList varList)
  | (c, varMono) <- toList varPoly
  ]
