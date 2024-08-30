{-# LANGUAGE NoStarIsType  #-}
{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.Plonkup.Relation where

import           Data.Bool                                           (bool)
import           Data.Map                                            (Map, elems, keys)
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
import           ZkFold.Base.Protocol.Plonkup.LookupConstraint       (LookupConstraint (..))
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint        (PlonkConstraint (..), toPlonkConstraint)
import           ZkFold.Base.Protocol.Plonkup.PlonkupConstraint
import           ZkFold.Prelude                                      (length, replicate)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

-- Here `n` is the total number of constraints, `i` is the number of inputs to the circuit, and `a` is the field type.
data PlonkupRelation n i a = PlonkupRelation
    { qM    :: PolyVec a n
    , qL    :: PolyVec a n
    , qR    :: PolyVec a n
    , qO    :: PolyVec a n
    , qC    :: PolyVec a n
    , qK    :: PolyVec a n
    , t     :: PolyVec a n
    , sigma :: Permutation (3 * n)
    , wmap  :: Vector i a -> Map Natural a -> (PolyVec a n, PolyVec a n, PolyVec a n)
    }

toPlonkupRelation :: forall i n l a .
       KnownNat i
    => KnownNat n
    => KnownNat (3 * n)
    => KnownNat l
    => Arithmetic a
    => Vector l (Var (Vector i))
    -> ArithmeticCircuit a (Vector i) Par1
    -> Maybe (PlonkupRelation n i a)
toPlonkupRelation xPub ac =
    let pubInputConstraints = map var (fromVector xPub)
        plonkConstraints    = elems (acSystem ac)
        rs = map (toConstant @_ @Natural) $ elems $ acRange ac
        t = toPolyVec $ fromList $ map fromConstant $ bool [] (replicate (value @n -! length rs + 1) 0 ++ [ 0 .. head rs ]) (not $ null rs)
        nLookup = bool 0 (head rs + 1) (not $ null rs)
        xLookup = NewVar <$> keys (acRange ac)

        n'      = acSizeN ac + value @l + nLookup

        plonkupSystem = concat
            [ map (ConsPlonk . toPlonkConstraint) (pubInputConstraints ++ plonkConstraints)
            , ConsLookup . LookupConstraint <$> xLookup
            , replicate (value @n -! n') ConsExtra
            ]

        qM = toPolyVec @a @n $ fromList $ map (qm . getPlonkConstraint) plonkupSystem
        qL = toPolyVec @a @n $ fromList $ map (ql . getPlonkConstraint) plonkupSystem
        qR = toPolyVec @a @n $ fromList $ map (qr . getPlonkConstraint) plonkupSystem
        qO = toPolyVec @a @n $ fromList $ map (qo . getPlonkConstraint) plonkupSystem
        qC = toPolyVec @a @n $ fromList $ map (qc . getPlonkConstraint) plonkupSystem
        qK = toPolyVec @a @n $ fromList $ map isLookupConstraint plonkupSystem

        a  = map getA plonkupSystem
        b  = map getB plonkupSystem
        c  = map getC plonkupSystem
        -- TODO: Permutation code is not particularly safe. We rely on the list being of length 3*n.
        sigma = fromCycles @(3*n) $ mkIndexPartition $ fromList $ a ++ b ++ c

        w1 i   = toPolyVec $ fromList $ map (indexW ac i) a
        w2 i   = toPolyVec $ fromList $ map (indexW ac i) b
        w3 i   = toPolyVec $ fromList $ map (indexW ac i) c
        wmap i _ = (w1 i, w2 i, w3 i)

    in if n' <= value @n
        then Just $ PlonkupRelation {..}
        else Nothing

toPlonkRelation :: forall i n l a .
       KnownNat i
    => KnownNat n
    => KnownNat (3 * n)
    => KnownNat l
    => Arithmetic a
    => Vector l (Var (Vector i))
    -> ArithmeticCircuit a (Vector i) Par1
    -> Maybe (PlonkupRelation n i a)
toPlonkRelation xPub ac0 =
    let ac = desugarRanges ac0
    in toPlonkupRelation xPub ac
