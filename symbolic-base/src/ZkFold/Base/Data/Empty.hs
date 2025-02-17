{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Data.Empty where

import           Data.Function    (const, ($))
import           Data.Functor.Rep (Representable (..))
import           GHC.Generics     (U1 (..), (:*:) (..), (:.:) (..))

class Empty f where
  empty :: f a

instance Empty U1 where
  empty = U1

instance (Empty f, Empty g) => Empty (f :*: g) where
  empty = empty :*: empty

instance (Representable f, Empty g) => Empty (f :.: g) where
  empty = Comp1 $ tabulate (const empty)
