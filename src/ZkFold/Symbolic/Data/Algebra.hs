module ZkFold.Symbolic.Data.Algebra where

import           Data.Functor.Identity           (Identity (..))
import           Numeric.Natural                 (Natural)
import           Prelude                         (Integer)
import qualified Prelude                         as Prelude

import qualified ZkFold.Base.Algebra.Basic.Class as Algebra

class MultiplicativeSemigroup a u where
  (*) :: u a -> u a -> u a

class MultiplicativeSemigroup a u => MultiplicativeMonoid a u where
  one :: u a
  (^) :: u a -> Natural -> u a
  _ ^ 0 = one
  x ^ 1 = x
  x ^ n =
    let
      (nOver2, evenOrOdd) = n `Prelude.divMod` 2
      sqrt = x ^ nOver2
      parity = x ^ evenOrOdd
    in
      sqrt * sqrt * parity

class AdditiveSemigroup a u where
  (+) :: u a -> u a -> u a

class AdditiveSemigroup a u => AdditiveMonoid a u where
  zero :: u a
  scaleNatural :: Natural -> u a -> u a
  scaleNatural n x = combineNatural [(n,x)]
  -- | linear combination, assuming commutativity of (+)
  combineNatural :: [(Natural, u a)] -> u a
  combineNatural [] = zero
  combineNatural xs =
    let
      halved = combineNatural [(n `Prelude.div` 2, x) | (n, x) <- xs, n Prelude.> 1]
      remainder = Prelude.foldl (+) zero [x | (n, x) <- xs, Prelude.odd n]
    in
      halved + halved + remainder

class AdditiveMonoid a u => AdditiveGroup a u where
  negate :: u a -> u a
  negate x = zero - x
  (-) :: u a -> u a -> u a
  x - y = x + negate y
  scaleInteger :: Integer -> u a -> u a
  scaleInteger n x = let (n',x') = absPair n x in scaleNatural n' x'
  combineInteger :: [(Integer, u a)] -> u a
  combineInteger xs = combineNatural [absPair n x | (n,x) <- xs]

absPair :: AdditiveGroup a u => Integer -> u a -> (Natural, u a)
absPair n x =
  if n Prelude.>= 0
    then (Prelude.fromIntegral n, x)
    else (Prelude.fromIntegral (Prelude.negate n), negate x)

type Semiring a u = (MultiplicativeMonoid a u, AdditiveMonoid a u, Algebra.FromConstant Natural (u a))
type Ring a u = (Semiring a u, AdditiveGroup a u, Algebra.FromConstant Integer (u a))

fromNatural :: Algebra.FromConstant Natural a => Natural -> a
fromNatural = Algebra.fromConstant

fromInteger :: Algebra.FromConstant Integer a => Integer -> a
fromInteger = Algebra.fromConstant

instance Algebra.MultiplicativeSemigroup a
  => MultiplicativeSemigroup a Identity where
    Identity x * Identity y = Identity (x Algebra.* y)
instance Algebra.MultiplicativeMonoid a
  => MultiplicativeMonoid a Identity where
    one = Identity Algebra.one
    Identity x ^ n = Identity (x Algebra.^ n)
instance Algebra.AdditiveSemigroup a  => AdditiveSemigroup a Identity where
  Identity x + Identity y = Identity (x Algebra.+ y)
instance Algebra.AdditiveMonoid a => AdditiveMonoid a Identity where
  zero = Identity Algebra.zero
  scaleNatural n (Identity x) = Identity (Algebra.scale n x)
instance Algebra.AdditiveGroup a => AdditiveGroup a Identity where
  negate (Identity x) = Identity (Algebra.negate x)
  Identity x - Identity y = Identity (x Algebra.- y)
  scaleInteger n (Identity x) = Identity (Algebra.scale n x)
