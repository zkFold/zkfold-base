{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Relation where

import           Data.Binary                                         (Binary)
import           Data.Bool                                           (bool)
import           Data.Constraint                                     (withDict)
import           Data.Constraint.Nat                                 (timesNat)
import           Data.Map                                            (elems, keys)
import           Data.Maybe                                          (fromJust)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, replicate, sum,
                                                                      take, (!!), (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations              (Permutation, fromCycles, mkIndexPartition)
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (evalMonomial, evalPolynomial, var)
import           ZkFold.Base.Algebra.Polynomials.Univariate          (PolyVec, toPolyVec)
import           ZkFold.Base.Data.Vector                             (Vector, fromVector)
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkupPermutationSize)
import           ZkFold.Base.Protocol.Plonkup.LookupConstraint       (LookupConstraint (..))
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint        (PlonkConstraint (..), toPlonkConstraint)
import           ZkFold.Base.Protocol.Plonkup.PlonkupConstraint
import           ZkFold.Prelude                                      (length, replicate)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

-- Here `n` is the total number of constraints, `i` is the number of inputs to the circuit, and `a` is the field type.
data PlonkupRelation i n l a = PlonkupRelation
    { qM       :: PolyVec a n
    , qL       :: PolyVec a n
    , qR       :: PolyVec a n
    , qO       :: PolyVec a n
    , qC       :: PolyVec a n
    , qK       :: PolyVec a n
    , t        :: PolyVec a n
    , sigma    :: Permutation (3 * n)
    , witness  :: Vector i a -> (PolyVec a n, PolyVec a n, PolyVec a n)
    , pubInput :: Vector i a -> Vector l a
    }

instance Show a => Show (PlonkupRelation i n l a) where
    show PlonkupRelation {..} =
        "Plonkup Relation: "
        ++ show qM ++ " "
        ++ show qL ++ " "
        ++ show qR ++ " "
        ++ show qO ++ " "
        ++ show qC ++ " "
        ++ show qK ++ " "
        ++ show t ++ " "
        ++ show sigma

instance
        ( KnownNat i
        , KnownNat n
        , KnownNat (PlonkupPermutationSize n)
        , KnownNat l
        , Arbitrary a
        , Arithmetic a
        , Binary a
        ) => Arbitrary (PlonkupRelation i n l a) where
    arbitrary = fromJust . toPlonkupRelation <$> arbitrary

toPlonkupRelation :: forall i n l a .
       KnownNat i
    => KnownNat n
    => KnownNat l
    => Arithmetic a
    => ArithmeticCircuit a (Vector i) (Vector l)
    -> Maybe (PlonkupRelation i n l a)
toPlonkupRelation ac =
    let xPub                = acOutput ac
        pubInputConstraints = map var (fromVector xPub)
        plonkConstraints    = map (evalPolynomial evalMonomial (var . SysVar)) (elems (acSystem ac))
        rs = map toConstant $ elems $ acRange ac
        -- TODO: We are expecting at most one range.
        t = toPolyVec $ fromList $ map fromConstant $ bool [] (replicate (value @n -! length rs + 1) 0 ++ [ 0 .. head rs ]) (not $ null rs)
        -- Number of elements in the set `t`.
        nLookup = bool 0 (head rs + 1) (not $ null rs)
        -- Lookup queries.
        xLookup = keys (acRange ac)

        -- The total number of constraints in the relation.
        n'      = acSizeN ac + value @l + length xLookup

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
        sigma = withDict (timesNat @3 @n) (fromCycles @(3*n) $ mkIndexPartition $ fromList $ a ++ b ++ c)

        w1 i   = toPolyVec $ fromList $ fmap (indexW ac i) a
        w2 i   = toPolyVec $ fromList $ fmap (indexW ac i) b
        w3 i   = toPolyVec $ fromList $ fmap (indexW ac i) c
        witness i  = (w1 i, w2 i, w3 i)
        pubInput i = fmap (indexW ac i) xPub

    in if max n' nLookup <= value @n
        then Just $ PlonkupRelation {..}
        else Nothing
