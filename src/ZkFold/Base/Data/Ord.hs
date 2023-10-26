{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Data.Ord where

import qualified Data.Bool                                   as Haskell
import           Prelude                                     (map, zipWith, ($))
import qualified Prelude                                     as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Data.Bool                       (BoolType (..), Bool (..))
import           ZkFold.Base.Data.Conditional                (Conditional(..), bool)
import           ZkFold.Base.Data.Eq                         (Eq(..))
import           ZkFold.Base.Protocol.Arithmetization.R1CS   (Arithmetizable, R1CS)

-- TODO: add `compare`
class Ord b a where
    (<=) :: a -> a -> b

    (<) :: a -> a -> b

    (>=) :: a -> a -> b

    (>) :: a -> a -> b

    max :: a -> a -> a
    -- max x y = bool @b y x $ x <= y

    min :: a -> a -> a
    -- min x y = bool @b y x $ x >= y

instance Haskell.Ord a => Ord Haskell.Bool a where
    (<=) = (Haskell.<=)

    (<) = (Haskell.<)

    (>=) = (Haskell.>=)

    (>) = (Haskell.>)

    max = Haskell.max

    min = Haskell.min

instance (Prime p, Haskell.Ord x) => Ord (Bool (Zp p)) x where
    x <= y = Bool $ Haskell.bool zero one (x Haskell.<= y)

    x <  y = Bool $ Haskell.bool zero one (x Haskell.<  y)

    x >= y = Bool $ Haskell.bool zero one (x Haskell.>= y)

    x >  y = Bool $ Haskell.bool zero one (x Haskell.>  y)

    max x y = Haskell.bool y x $ x <= y

    min x y = Haskell.bool y x $ x >= y

instance (Arithmetizable a (R1CS a)) => Ord (Bool (R1CS a)) (R1CS a) where
    x <= y =
        let bEQ = zipWith (-) (toBits y) (toBits x)
            bGT = map (\b -> b - one) bEQ
        in checkBits bGT bEQ

    x < y = (x <= y) && (x /= y)

    x >= y = y <= x

    x > y = y < x

    max x y = bool @(Bool (R1CS a)) y x $ x <= y

    min x y = bool @(Bool (R1CS a)) y x $ x >= y

checkBits :: forall b x . (FiniteField x, Conditional b b, Eq b x) => [x] -> [x] -> b
checkBits []     _      = false
checkBits _      []     = false
checkBits (x:xs) (y:ys) = bool @b ((y == zero) && checkBits xs ys) true (x == zero)