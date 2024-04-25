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

class AdditiveSemigroup a u where
  (+) :: u a -> u a -> u a

class AdditiveSemigroup a u => AdditiveMonoid a u where
  zero :: u a
  scaleNatural :: Natural -> u a -> u a
  scaleNatural n x = combineNatural [(n,x)]
  -- | linear combination using double-and-add,
  -- and assuming commutativity of (+),
  -- log(n1 + .. + nk) complexity
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

class (MultiplicativeMonoid a u, AdditiveMonoid a u) => Semiring a u where
  fromNatural :: Natural -> u a

class (Semiring a u, AdditiveGroup a u) => Ring a u where
  fromInteger :: Integer -> u a

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
instance Algebra.Semiring a => Semiring a Identity where
  fromNatural n = Identity (Algebra.fromConstant n)
instance Algebra.Ring a => Ring a Identity where
  fromInteger n = Identity (Algebra.fromConstant n)
