{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.Ord (Ord (..)) where

import           Control.Monad.State                                    (evalState)
import qualified Data.Bool                                              as Haskell
import           Prelude                                                (concatMap, flip, mempty, reverse, zipWith, ($), (.))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                        (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (plusMultC)
import           ZkFold.Symbolic.Data.Bool                              (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Conditional                       (Conditional (..))
import           ZkFold.Symbolic.Data.DiscreteField                     (DiscreteField (..))

-- TODO (Issue #23): add `compare`
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

    max x y = Haskell.bool x y $ x <= y

    min x y = Haskell.bool x y $ x >= y

-- | Every @Arithmetizable@ type can be compared lexicographically.
instance Arithmetizable a x => Ord (Bool (ArithmeticCircuit a)) x where
    x <= y = y >= x

    x <  y = y > x

    x >= y = bitCheckGE dorAnd $ zipWith (-) (getBitsBE @a x) (getBitsBE y)

    x >  y = bitCheckGT dorAnd $ zipWith (-) (getBitsBE @a x) (getBitsBE y)

    max x y = bool @(Bool (ArithmeticCircuit a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit a)) x y $ x > y

getBitsBE :: Arithmetizable a x => x -> [ArithmeticCircuit a]
-- ^ @getBitsBE x@ returns a list of circuits computing bits of @x@, eldest to
-- youngest.
getBitsBE = concatMap (reverse . toBits) . flip evalState mempty . arithmetize

dorAnd ::
  (FiniteField a, Haskell.Eq a, ToBits a) =>
  Bool (ArithmeticCircuit a) ->
  Bool (ArithmeticCircuit a) ->
  Bool (ArithmeticCircuit a) ->
  Bool (ArithmeticCircuit a)
-- ^ @dorAnd a b c@ is a schema which computes @a || b && c@ given @a && b@ is
-- false.
dorAnd (Bool a) (Bool b) (Bool c) = Bool (plusMultC a b c)

bitCheckGE :: DiscreteField b x => (b -> b -> b -> b) -> [x] -> b
-- ^ @bitCheckGE plm ds@ checks if @ds@ contains delta lexicographically greater
-- than or equal to 0, given @plm a b c = a || b && c@ when @a && b@ is false.
bitCheckGE _   []     = true
bitCheckGE _   [d]    = isZero ((d - one) * d)
bitCheckGE plm (d:ds) = plm (isZero $ d - one) (isZero d) (bitCheckGE plm ds)

bitCheckGT :: DiscreteField b x => (b -> b -> b -> b) -> [x] -> b
-- ^ @bitCheckGT plm ds@ checks if @ds@ contains delta lexicographically greater
-- than 0, given @plm a b c = a || b && c@ when @a && b@ is false.
bitCheckGT _   []     = false
bitCheckGT _   [d]    = isZero (d - one)
bitCheckGT plm (d:ds) = plm (isZero $ d - one) (isZero d) (bitCheckGT plm ds)
