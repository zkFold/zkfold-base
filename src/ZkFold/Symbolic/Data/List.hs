module ZkFold.Symbolic.Data.List where

import           Data.Kind                                              (Type)
import           GHC.TypeNats                                           (Natural)
import           Prelude                                                (undefined)

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance    ()
import           ZkFold.Symbolic.Data.FieldElement                      (FieldElementData(..))

data List (context :: Natural -> Type -> Type) (a :: Type) x = List (context (TypeSize a context x) a) (context 1 a)

infixr 5 .:
(.:) :: List context a x -> x -> List context a x
_ .: _ = undefined

uncons :: List context a x -> (x, List context a x)
uncons = undefined

head :: List context a x -> x
head xs = let (x, _) = uncons xs in x

tail :: List context a x -> List context a x
tail xs = let (_, xs') = uncons xs in xs'

(++) :: List context a x -> List context a x -> List context a x
_ ++ _ = undefined
