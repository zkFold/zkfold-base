module ZkFold.Symbolic.Data.Int where

import ZkFold.Symbolic.Data.Bool (Bool, BoolType (..))
import ZkFold.Symbolic.Data.UInt (UInt)
import Data.Kind (Type)
import ZkFold.Base.Algebra.Basic.Number (Natural, KnownNat)
import ZkFold.Symbolic.Data.Combinators (RegisterSize, KnownRegisterSize)
import ZkFold.Symbolic.Class
import ZkFold.Symbolic.Data.Eq

import qualified Prelude as Haskell


data Int (n :: Natural) (r :: RegisterSize) (context :: (Type -> Type) -> Type) =
    Int {
    sign :: Bool context,
    num :: UInt n r context
    }

instance (Symbolic c, KnownNat n, KnownRegisterSize r) => Eq (Bool c) (Int n r c) where
    (==) (Int b1 n1) (Int b2 n2) = (b1 == b2) && (n1 == n2)