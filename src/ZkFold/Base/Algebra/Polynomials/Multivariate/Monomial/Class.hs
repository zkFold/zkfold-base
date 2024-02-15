module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial.Class where

import           Data.Map                          (Map)
import qualified Data.Map                          as Map
import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)

import           ZkFold.Base.Algebra.Basic.Class

type Variable i = Ord i

type Monomial i j = (Variable i, Eq j, Ord j, Ring j)

class Monomial i j => FromMonomial i j m where
    fromMonomial :: m -> Map i j

instance Monomial i j => FromMonomial i j (Map i j) where
    fromMonomial = id

class Monomial i j => ToMonomial i j m where
    toMonomial   :: Map i j -> Maybe m

instance Monomial i j => ToMonomial i j (Map i j) where
    toMonomial   = Just . Map.filter (/= zero)