{-# OPTIONS_GHC -fno-warn-orphans #-}
module ZkFold.Symbolic.Data.Char where

import           Prelude
import           GHC.TypeNats                 (Natural)
import           Data.Char                    (ord)
import           Data.String                  (IsString (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Data.UInt

type ASCIIChar a = UInt 7 a

instance (Finite a, AdditiveMonoid a, FromConstant Natural a) => IsString (Vector n (ASCIIChar a)) where
    fromString x = Vector (fromConstant . toEnum @Natural . ord <$> x)
