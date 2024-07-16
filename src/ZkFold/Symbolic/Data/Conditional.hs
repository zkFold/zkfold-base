module ZkFold.Symbolic.Data.Conditional where

import qualified Data.Bool                         as Haskell
import           Data.Eq                           ((==))
import           Data.Function                     (($))
import           Data.Zip                          (zipWith)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Base.Algebra.Basic.Number  (KnownNat)
import           ZkFold.Base.Data.Vector           (Vector, item)
import           ZkFold.Symbolic.Data.Bool         (Bool (Bool), BoolType (..))
import           ZkFold.Symbolic.Data.FieldElement

class BoolType b => Conditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance KnownNat p => Conditional (Bool (Zp p)) (Zp p) where
    bool x y b = Haskell.bool x y (b == true)

instance FieldElementData a Vector x => Conditional (Bool (Vector 1 a)) x where
    bool x y (Bool b) =
      let b' = item b
       in fromFieldElements @a
          $ zipWith (\x' y' -> (one - b') * x' + b' * y')
              (toFieldElements @a @Vector x)
              (toFieldElements @a y)
