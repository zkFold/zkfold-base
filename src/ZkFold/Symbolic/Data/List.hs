module ZkFold.Symbolic.Data.List where

import           Data.Foldable                     (Foldable (..))
import           Data.Kind                         (Type)
import           GHC.TypeNats                      (Natural)
import           Prelude                           (flip, undefined, (.))

import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.FieldElement (FieldElementData (..))

data List (context :: Natural -> Type) x = List (context (TypeSize context x)) (context 1)

emptyList :: List context x
emptyList = undefined

-- TODO: we should implement an optimized version of `null`

infixr 5 .:
(.:) :: x -> List context x -> List context x
_ .: _ = undefined

uncons :: List context x -> (x, List context x)
uncons = undefined

head :: List context x -> x
head xs = let (x, _) = uncons xs in x

tail :: List context x -> List context x
tail xs = let (_, xs') = uncons xs in xs'

reverse :: Foldable (List context) => List context x -> List context x
reverse = foldl (flip (.:)) emptyList

init :: Foldable (List context) => List context x -> List context x
init = reverse . tail . reverse

last :: Foldable (List context) => List context x -> x
last = head . reverse

(++) :: List context x -> List context x -> List context x
_ ++ _ = undefined

filter ::
       (x -> Bool (context 1))
    -> List context x
    -> List context x
filter = undefined
