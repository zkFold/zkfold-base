module ZkFold.Base.Data.Boolean
  ( Boolean (..)
  , all, any, and, or
  ) where

import           Control.Category
import qualified Data.Bool                        as H
import           Data.Foldable                    hiding (all, and, any, elem, or)
import qualified Prelude                          as H

class Boolean b where
  true, false :: b
  not :: b -> b
  (&&), (||), xor :: b -> b -> b

instance Boolean H.Bool where
  true = H.True
  false = H.False
  not = H.not
  (&&) = (H.&&)
  (||) = (H.||)
  xor = (H./=)

all :: (Boolean b, Foldable t) => (x -> b) -> t x -> b
all f = foldr ((&&) . f) true

any :: (Boolean b, Foldable t) => (x -> b) -> t x -> b
any f = foldr ((||) . f) false

and :: (Boolean b, Foldable t) => t b -> b
and = all id

or :: (Boolean b, Foldable t) => t b -> b
or = any id
