{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Data.Vector
  ( Vector
  , (:.:) (..)
  , (!!)
  , generate
  ) where

import           Data.Functor.Rep
import           GHC.Generics hiding (Rep)

import           ZkFold.Base.Data.Vector hiding ((!!))

-- | unsafe indexing (out-of-bounds error)
(!!) :: Representable vector => (vector :.: u) a -> Rep vector -> u a
Comp1 f !! ix = index f ix

-- | safe tabulation
generate :: Representable vector => (Rep vector -> u a) -> (vector :.: u) a
generate f = Comp1 (tabulate f)
