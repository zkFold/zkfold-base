{-# LANGUAGE NoStarIsType  #-}
{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.ARK.Plonk.Relation where

import           Data.Map                                     (Map, elems, (!))
import           GHC.Generics                                 (Par1)
import           GHC.IsList                                   (IsList (..))
import           Numeric.Natural                              (Natural)
import           Prelude                                      hiding (Num (..), drop, length, replicate, sum, take,
                                                               (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations       (Permutation, fromCycles, mkIndexPartition)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (evalMonomial, evalPolynomial, var)
import           ZkFold.Base.Algebra.Polynomials.Univariate   (PolyVec, toPolyVec)
import           ZkFold.Base.Data.Vector                      (Vector, fromVector)
import           ZkFold.Base.Protocol.ARK.Plonk.Constraint    (PlonkConstraint (..), toPlonkConstraint)
import           ZkFold.Prelude                               (replicate)
import           ZkFold.Symbolic.Compiler

-- Here `n` is the total number of constraints, `l` is the number of public inputs, and `a` is the field type.
data PlonkRelation n l a = PlonkRelation
    { qM    :: PolyVec a n
    , qL    :: PolyVec a n
    , qR    :: PolyVec a n
    , qO    :: PolyVec a n
    , qC    :: PolyVec a n
    , sigma :: Permutation (3 * n)
    , wmap  :: Map Natural a -> (PolyVec a n, PolyVec a n, PolyVec a n)
    }

toPlonkRelation :: forall n l a .
       KnownNat n
    => KnownNat (3 * n)
    => KnownNat l
    => Arithmetic a
    => Scale a a
    => FromConstant a a
    => Vector l Natural
    -> ArithmeticCircuit a Par1
    -> Maybe (PlonkRelation n l a)
toPlonkRelation xPub ac0 =
    let ac = desugarRanges ac0
        evalX0 = evalPolynomial evalMonomial (\x -> if x == 0 then one else var x)

        pubInputConstraints = map var (fromVector xPub)
        acConstraints       = map evalX0 $ elems (constraintSystem ac)
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

        wmap'  = witnessGenerator ac
        w1 i   = toPolyVec $ fromList $ map (wmap' i !) a
        w2 i   = toPolyVec $ fromList $ map (wmap' i !) b
        w3 i   = toPolyVec $ fromList $ map (wmap' i !) c
        wmap i = (w1 i, w2 i, w3 i)

    in if (acSizeN ac + value @l) <= value @n
        then Just $ PlonkRelation {..}
        else Nothing
