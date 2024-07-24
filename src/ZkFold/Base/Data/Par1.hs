{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Data.Par1 where

import           Data.Semialign (Semialign (..))
import           Data.These     (These (These))
import           Data.Zip       (Zip (..))
import           GHC.Generics   (Par1 (..))

instance Semialign Par1 where
  align (Par1 x) (Par1 y) = Par1 (These x y)

instance Zip Par1 where
  zip (Par1 x) (Par1 y) = Par1 (x, y)
