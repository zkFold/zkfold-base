module ZkFold.Symbolic.Data.Conditional where

import           Data.Monoid               (First (..))
import           Prelude                   hiding (Bool, Num (..), (/))

import           ZkFold.Symbolic.Data.Bool (Bool (..), BoolType (..))

class BoolType b => Conditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance {-# OVERLAPPABLE #-} (BoolType b, Eq b) => Conditional b x where
    bool f t b = if b == true then t else f

find :: forall a t tt .
    Foldable tt =>
    Conditional (Bool a) (Maybe (t a)) =>
    tt (t a) -> (t a -> Bool a) -> Maybe (t a)
find xs p = getFirst $ foldMap (\x -> First . bool @(Bool a) (Just x) Nothing $ p x) xs
