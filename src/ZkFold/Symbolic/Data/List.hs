{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Data.List where

import           Data.FixedLength            hiding (List)
import qualified Data.NonEmpty               as NonEmpty
import           Prelude                     (Integer, Applicative (..), Num (..), ($))
import           Type.Data.Num.Unary         (Natural)
import           Type.Data.Num.Unary.Literal (U0)

import           ZkFold.Prelude              (length)

type GE16 n = GE8 (GE8 n)
type U32 = GE16 (GE16 U0)

type List n x = T n x

indicesInteger :: Natural n => List n Integer
indicesInteger = NonEmpty.init $ NonEmpty.scanl (+) 0 $ pure 1

mapList :: Natural n => (a -> b) -> List n a -> List n b
mapList = Data.FixedLength.map

lengthList :: forall n . Natural n => Integer
lengthList = length $ toList (indices :: List n (Index n))