{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Algorithms.Hash.MiMC where

import           Data.List.NonEmpty                                     (NonEmpty ((:|)), nonEmpty)
import           Numeric.Natural                                        (Natural)
import           Prelude                                                hiding (Eq (..), Num (..), any, length, not,
                                                                         (!!), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                                (fromVector, singleton)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators
import           ZkFold.Symbolic.Data.FieldElement                      (FieldElement (..), FieldElementData (..))
import           ZkFold.Symbolic.Interpreter                            (Interpreter (..))

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash2 :: (FromConstant a x, Ring x) => [a] -> a -> x -> x -> x
mimcHash2 (map fromConstant -> xs) (fromConstant -> k) = case nonEmpty (reverse xs) of
    Just cs -> go cs
    Nothing -> error "mimcHash: empty list"
    where
        go (c :| cs) xL xR =
          let t5 = (xL + k + c) ^ (5 :: Natural)
           in case nonEmpty cs of
              Just cs' -> go cs' (xR + t5) xL
              Nothing  -> xR + t5

mimcHashN :: (FromConstant a x, Ring x) => [a] -> a -> [x] -> x
mimcHashN xs k = go
  where
    go zs = case zs of
      []          -> mimcHash2 xs k zero zero
      [z]         -> mimcHash2 xs k zero z
      [zL, zR]    -> mimcHash2 xs k zL zR
      (zL:zR:zs') -> go (mimcHash2 xs k zL zR : zs')

class MiMCHash a b x where
    mimcHash :: [a] -> a -> x -> FieldElement b a

instance FieldElementData a Vector x => MiMCHash a Vector x where
    mimcHash xs k = FieldElement . singleton . mimcHashN xs k . fromVector . runInterpreter . toFieldElements

instance FieldElementData a ArithmeticCircuit x => MiMCHash a ArithmeticCircuit x where
    mimcHash xs k = FieldElement . Interpreter . mimcHashN xs k . fromVector . splitCircuit . toFieldElements @a
