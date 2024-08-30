module ZkFold.Base.Protocol.Plonkup.PlonkupConstraint where

import           Prelude                                             hiding (Num (..), drop, length, replicate, sum,
                                                                      take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.Plonkup.LookupConstraint       (LookupConstraint (..))
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint        (PlonkConstraint (..), toPlonkConstraint)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

data PlonkupConstraint i a = ConsPlonk (PlonkConstraint i a) | ConsLookup (LookupConstraint i a) | ConsExtra

getPlonkConstraint :: (Eq a, FiniteField a, KnownNat i) => PlonkupConstraint i a -> PlonkConstraint i a
getPlonkConstraint (ConsPlonk c) = c
getPlonkConstraint _             = toPlonkConstraint zero

isLookupConstraint :: FiniteField a => PlonkupConstraint i a -> a
isLookupConstraint (ConsLookup _) = one
isLookupConstraint _              = zero

getA :: forall a i . (Eq a, FiniteField a, KnownNat i) => PlonkupConstraint i a -> Var (Vector i)
getA (ConsPlonk c)  = x1 c
getA (ConsLookup c) = lkVar c
getA ConsExtra      = x1 (toPlonkConstraint @a zero)

getB :: forall a i . (Eq a, FiniteField a, KnownNat i) => PlonkupConstraint i a -> Var (Vector i)
getB (ConsPlonk c)  = x2 c
getB (ConsLookup c) = lkVar c
getB ConsExtra      = x2 (toPlonkConstraint @a zero)

getC :: forall a i . (Eq a, FiniteField a, KnownNat i) => PlonkupConstraint i a -> Var (Vector i)
getC (ConsPlonk c)  = x3 c
getC (ConsLookup c) = lkVar c
getC ConsExtra      = x3 (toPlonkConstraint @a zero)
