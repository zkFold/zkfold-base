{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Cardano.UPLC.Inference.Internal where

import           Data.List                             (find)
import           Prelude

import           ZkFold.Symbolic.Cardano.UPLC.Term
import           ZkFold.Symbolic.Cardano.UPLC.Type

type TypeList name fun a = [(Term name fun a, SomeType a)]

updateTermType :: (Eq name, Eq fun) =>
    (Term name fun a, SomeType a) -> (Term name fun a, SomeType a) -> (Term name fun a, SomeType a)
updateTermType (term1, t1) (term2, t2) = if term1 == term2 then (term1, t1 <> t2) else (term1, t1)

makeTermList :: (Eq name, Eq fun) => Term name fun a -> [Term name fun a]
makeTermList (Var x) = [Var x]
makeTermList (LamAbs x f) = LamAbs x f : makeTermList f
makeTermList (Apply f x) = Apply f x : makeTermList f ++ makeTermList x
makeTermList (Force x) = Force x : makeTermList x
makeTermList (Delay x) = Delay x : makeTermList x
makeTermList (Constant x) = [Constant x]
makeTermList (Builtin x) = [Builtin x]
makeTermList Error = [Error]

makeTypeList :: (Eq name, Eq fun) => Term name fun a -> TypeList name fun a
makeTypeList = map (, NoType) . makeTermList

findTermType :: (Eq name, Eq fun) => Term name fun a -> TypeList name fun a -> Maybe (SomeType a)
findTermType term = fmap snd . find ((== term) . fst)

findLambda :: (Eq name) => name -> TypeList name fun a -> Maybe (Term name fun a)
findLambda x = fmap fst . find (isLambda . fst)
    where isLambda (LamAbs y _) = x == y
          isLambda _            = False

updateTypeList :: (Eq name, Eq fun) => TypeList name fun a -> TypeList name fun a -> TypeList name fun a
updateTypeList xs [] = xs
updateTypeList xs ((term, t):ys) = updateTypeList (map (updateTermType (term, t)) xs) ys