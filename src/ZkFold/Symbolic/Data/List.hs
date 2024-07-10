module ZkFold.Symbolic.Data.List where

import           Data.Foldable                     (Foldable(..))
import           Data.Kind                         (Type)
import           GHC.TypeNats                      (Natural)
import           Prelude                           (undefined, (.), flip)

import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.FieldElement (FieldElementData(..))

data List (context :: Natural -> Type -> Type) (a :: Type) x = List (context (TypeSize a context x) a) (context 1 a)

emptyList :: List context a x
emptyList = undefined

-- TODO: we should implement an optimized version of `null`

infixr 5 .:
(.:) :: x -> List context a x -> List context a x
_ .: _ = undefined

uncons :: List context a x -> (x, List context a x)
uncons = undefined

head :: List context a x -> x
head xs = let (x, _) = uncons xs in x

tail :: List context a x -> List context a x
tail xs = let (_, xs') = uncons xs in xs'

reverse :: Foldable (List context a) => List context a x -> List context a x
reverse = foldl (flip (.:)) emptyList

init :: Foldable (List context a) => List context a x -> List context a x
init = reverse . tail . reverse

last :: Foldable (List context a) => List context a x -> x
last = head . reverse

(++) :: List context a x -> List context a x -> List context a x
_ ++ _ = undefined

filter :: 
       (x -> Bool (context 1 a))
    -> List context a x
    -> List context a x
filter = undefined