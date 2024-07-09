{-# LANGUAGE DerivingStrategies   #-}

module ZkFold.Symbolic.Data.List where

import           Prelude                                                (undefined)

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance    ()
import           ZkFold.Symbolic.Data.Bool

newtype List context a = List (context a)

infixr 5 .:
(.:) :: List context a -> x -> List context a
_ .: _ = undefined

uncons :: List context a -> (x, List context a)
uncons = undefined

head :: List context a -> x
head xs = let (x, _) = uncons xs in x

tail :: List context a -> List context a
tail xs = let (_, xs') = uncons xs in xs'

null :: List context a -> Bool (context a)
null = undefined

foldl :: (x -> a -> x) -> x -> List context a -> x
foldl = undefined