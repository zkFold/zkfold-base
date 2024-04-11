module ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution where

import           Data.Map                                              (Map, lookup)
import           Prelude                                               hiding (Num (..), length, lookup, product, replicate, sum, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Field                       (Zp, fromZp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Data.Vector                               (Vector, fromVector)
import           ZkFold.Prelude                                        ((!!))

-- | Data structure `s` can be viewed as a substitution from `i` to `b`
class Substitution s i b where
  subs :: s -> (i -> b)

instance (Variable i) => Substitution (Map i b) i (Maybe b) where
  subs = flip lookup

instance Substitution (Vector n b) (Zp n) b where
  subs v i = fromVector v !! fromZp i
