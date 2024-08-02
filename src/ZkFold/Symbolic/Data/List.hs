module ZkFold.Symbolic.Data.List where

import           Data.Foldable              (Foldable (..))
import           Data.Kind                  (Type)
import           GHC.Generics               (Par1)
import           Prelude                    (flip, undefined, (.))

import           ZkFold.Base.Data.Vector    (Vector)
import           ZkFold.Symbolic.Data.Bool  (Bool)
import           ZkFold.Symbolic.Data.Class

data List (context :: (Type -> Type) -> Type) x = List (context (Vector (TypeSize context x))) (context Par1)

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
       (x -> Bool context)
    -> List context x
    -> List context x
filter = undefined
