{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.AlgebraicMap (AlgebraicMap (..), algebraicMap) where

import           Data.ByteString                                     (ByteString)
import           Data.Functor.Rep                                    (Representable (..))
import           Data.List                                           (foldl')
import           Data.Map.Strict                                     (Map, keys)
import qualified Data.Map.Strict                                     as M
import           Prelude                                             (fmap, zip, ($), (.), (<$>))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate        as PM
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.IVC.Predicate                  (Predicate (..))
import           ZkFold.Symbolic.Class                               (Symbolic(..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Eq

-- | Algebraic map of @a@.
-- It calculates a system of equations defining @a@ in some way.
-- The inputs are polymorphic in a ring element @f@.
-- The main application is to define the verifier's algebraic map in the NARK protocol.
--
newtype AlgebraicMap k i f = AlgebraicMap {
        applyAlgebraicMap :: i f -> Vector k [f] -> Vector (k-1) f -> f -> [f]
    }

algebraicMap :: forall d k i p f ctx .
    ( KnownNat (d+1)
    , Representable i
    , Ring f
    , Scale (BaseField ctx) f
    )
    => Predicate i p ctx
    -> AlgebraicMap k i f
algebraicMap Predicate {..} = AlgebraicMap algMap
    where
        sys :: [PM.Poly (BaseField ctx) (SysVar i) Natural]
        sys = M.elems (acSystem predicateCircuit)

        algMap :: i f -> Vector k [f] -> Vector (k-1) f -> f -> [f]
        algMap pi pm _ pad =
            let
                witness :: Map ByteString f
                witness = M.fromList $ zip (keys $ acWitness predicateCircuit) (V.head pm)

                varMap :: SysVar i -> f
                varMap (InVar inV)   = index pi inV
                varMap (NewVar newV) = M.findWithDefault zero newV witness

                f_sps :: Vector (d+1) [PM.Poly (BaseField ctx) (SysVar i) Natural]
                f_sps = degreeDecomposition @d $ sys

                f_sps_uni :: Vector (d+1) [f]
                f_sps_uni = fmap (PM.evalPolynomial PM.evalMonomial varMap) <$> f_sps
            in padDecomposition pad f_sps_uni

padDecomposition :: forall d f .
    ( MultiplicativeMonoid f
    , AdditiveMonoid f
    , KnownNat (d+1)
    ) => f -> V.Vector (d+1) [f] -> [f]
padDecomposition pad = foldl' (P.zipWith (+)) (P.repeat zero) . V.mapWithIx (\j p -> ((pad ^ (d -! j)) * ) <$> p)
    where
        d = value @(d+1) -! 1

-- | Decomposes an algebraic map into homogenous degree-j maps for j from 0 to @d@
--
degreeDecomposition :: forall d f v . KnownNat (d+1) => [Poly f v Natural] -> V.Vector (d+1) [Poly f v Natural]
degreeDecomposition lmap = tabulate (degree_j . toConstant)
    where
        degree_j :: Natural -> [Poly f v Natural]
        degree_j j = P.fmap (leaveDeg j) lmap

        leaveDeg :: Natural -> PM.Poly f v Natural -> PM.Poly f v Natural
        leaveDeg j (PM.P monomials) = PM.P $ P.filter (\(_, m) -> deg m == j) monomials

deg :: PM.Mono v Natural -> Natural
deg (PM.M m) = sum m
