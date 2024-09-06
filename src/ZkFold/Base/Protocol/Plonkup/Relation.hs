{-# LANGUAGE NoStarIsType  #-}
{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.Plonkup.Relation where

import           Data.Functor.Rep                                    (index)
import           Data.Map                                            (Map, elems, (!))
import           GHC.Generics                                        (Par1)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, replicate, sum,
                                                                      take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations              (Permutation, fromCycles, mkIndexPartition)
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (var)
import           ZkFold.Base.Algebra.Polynomials.Univariate          (PolyVec, toPolyVec)
import           ZkFold.Base.Data.Vector                             (Vector, fromVector)
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint        (PlonkConstraint (..), toPlonkConstraint)
import           ZkFold.Prelude                                      (replicate)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

-- Here `n` is the total number of constraints, `i` is the number of inputs to the circuit, and `a` is the field type.
data PlonkRelation n i a = PlonkRelation
    { qM    :: PolyVec a n
    , qL    :: PolyVec a n
    , qR    :: PolyVec a n
    , qO    :: PolyVec a n
    , qC    :: PolyVec a n
    , sigma :: Permutation (3 * n)
    , wmap  :: Vector i a -> Map Natural a -> (PolyVec a n, PolyVec a n, PolyVec a n)
    }

toPlonkRelation :: forall i n l a .
       KnownNat i
    => KnownNat n
    => KnownNat (3 * n)
    => KnownNat l
    => Arithmetic a
    => Scale a a
    => Vector l (Var (Vector i))
    -> ArithmeticCircuit a (Vector i) Par1
    -> Maybe (PlonkRelation n i a)
toPlonkRelation xPub ac0 =
    let ac = desugarRanges ac0

        pubInputConstraints = map var (fromVector xPub)
        acConstraints       = elems (acSystem ac)
        extraConstraints    = replicate (value @n -! acSizeN ac -! value @l) zero

        system = map toPlonkConstraint $ pubInputConstraints ++ acConstraints ++ extraConstraints

        qM = toPolyVec @a @n $ fromList $ map qm system
        qL = toPolyVec @a @n $ fromList $ map ql system
        qR = toPolyVec @a @n $ fromList $ map qr system
        qO = toPolyVec @a @n $ fromList $ map qo system
        qC = toPolyVec @a @n $ fromList $ map qc system

        a  = map x1 system
        b  = map x2 system
        c  = map x3 system
        -- TODO: Permutation code is not particularly safe. We rely on the list being of length 3*n.
        sigma = fromCycles @(3*n) $ mkIndexPartition $ fromList $ a ++ b ++ c

        indexW _ Nothing           = one
        indexW i (Just (InVar v))  = index i v
        indexW i (Just (NewVar v)) = witnessGenerator ac i ! v

        w1 i   = toPolyVec $ fromList $ map (indexW i) a
        w2 i   = toPolyVec $ fromList $ map (indexW i) b
        w3 i   = toPolyVec $ fromList $ map (indexW i) c
        wmap i _ = (w1 i, w2 i, w3 i)

    in if (acSizeN ac + value @l) <= value @n
        then Just $ PlonkRelation {..}
        else Nothing
