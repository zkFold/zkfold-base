{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Data.Ord where

import           Prelude                        (Bool, Integer, Ord, map, zipWith, ($))
import qualified Prelude                        as Haskell

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool                     (SymbolicBool (..), GeneralizedBoolean (..))
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional, bool)
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq(..))
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (Arithmetizable, R1CS)

-- TODO: add `compare`
class GeneralizedConditional b a => GeneralizedOrd b a where
    (<=) :: a -> a -> b

    (<) :: a -> a -> b

    (>=) :: a -> a -> b

    (>) :: a -> a -> b

    max :: a -> a -> a
    max x y = bool @b y x $ x <= y

    min :: a -> a -> a
    min x y = bool @b y x $ x >= y

instance Ord a => GeneralizedOrd Bool a where
    (<=) = (Haskell.<=)

    (<) = (Haskell.<)

    (>=) = (Haskell.>=)

    (>) = (Haskell.>)

instance (FromConstant Integer a, Arithmetizable a a Integer (R1CS a a Integer)) =>
        GeneralizedOrd (SymbolicBool (R1CS a a Integer)) (R1CS a a Integer) where
    x <= y =
        let bEQ = zipWith (-) (toBits y) (toBits x)
            bGT = map (\b -> b - one) bEQ
        in checkBits bGT bEQ

    x < y = (x <= y) && (x /= y)

    x >= y = y <= x

    x > y = y < x

checkBits :: forall b x . (FiniteField x, GeneralizedConditional b b, GeneralizedEq b x) => [x] -> [x] -> b
checkBits []     _      = false
checkBits _      []     = false
checkBits (x:xs) (y:ys) = bool @b ((y == zero) && checkBits xs ys) true (x == zero)