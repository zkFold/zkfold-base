module ZkFold.Base.Protocol.Plonkup.PlonkupConstraint where

import           Data.Functor.Rep                                    (Rep)
import           Prelude                                             hiding (Num (..), drop, length, replicate, sum,
                                                                      take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Protocol.Plonkup.LookupConstraint       (LookupConstraint (..))
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint        (PlonkConstraint (..), toPlonkConstraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Class    (toLinVar)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkupConstraint i a = ConsPlonk (PlonkConstraint i a) | ConsLookup (LookupConstraint i a) | ConsExtra

getPlonkConstraint :: (Ord a, FiniteField a, Ord (Rep i)) => PlonkupConstraint i a -> PlonkConstraint i a
getPlonkConstraint (ConsPlonk c) = c
getPlonkConstraint _             = toPlonkConstraint zero

isLookupConstraint :: FiniteField a => PlonkupConstraint i a -> a
isLookupConstraint (ConsLookup _) = one
isLookupConstraint _              = zero

getA :: forall a i . (Ord (Rep i), Arithmetic a) => PlonkupConstraint i a -> Var a i
getA (ConsPlonk c)  = x1 c
getA (ConsLookup c) = toLinVar $ lkVar c
getA ConsExtra      = x1 (toPlonkConstraint zero)

getB :: forall a i . (Ord (Rep i), Arithmetic a) => PlonkupConstraint i a -> Var a i
getB (ConsPlonk c)  = x2 c
getB (ConsLookup c) = toLinVar $ lkVar c
getB ConsExtra      = x2 (toPlonkConstraint zero)

getC :: forall a i . (Ord (Rep i), Arithmetic a) =>PlonkupConstraint i a -> Var a i
getC (ConsPlonk c)  = x3 c
getC (ConsLookup c) = toLinVar $ lkVar c
getC ConsExtra      = x3 (toPlonkConstraint zero)
