module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial.Class where

import           Data.Map                         (Map, fromListWith)
import qualified Data.Map                         as Map
import           Prelude                          hiding (Num (..), replicate, (/))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number (KnownNat)
import           ZkFold.Base.Data.Vector          (Vector, fromVector, toVector)
import           ZkFold.Prelude                   (replicate)

type Variable i = Ord i

type Monomial i j = (Variable i, Ord j, Semiring j)

----------------------------------- FromMonomial -----------------------------------

class (Monomial i j) => FromMonomial i j m where
  fromMonomial :: m -> Map i j

instance (Monomial i j) => FromMonomial i j (Map i j) where
  fromMonomial = id

instance (Monomial i Bool) => FromMonomial i Bool (Vector d (i, Bool)) where
  fromMonomial v = fromListWith (+) $ map (\(i, _) -> (i, one)) $ filter snd $ fromVector v

----------------------------------- ToMonomial -------------------------------------

class (Monomial i j) => ToMonomial i j m where
  toMonomial :: Map i j -> Maybe m

instance (Monomial i j) => ToMonomial i j (Map i j) where
  toMonomial = Just . Map.filter (/= zero)

instance (Monomial i j, Integral j, KnownNat d) => ToMonomial i j (Vector d (i, Bool)) where
  toMonomial m =
    let v = foldl (\acc (i, j) -> acc ++ replicate (fromIntegral j) (i, True)) [] $ Map.toList m
     in toVector v
