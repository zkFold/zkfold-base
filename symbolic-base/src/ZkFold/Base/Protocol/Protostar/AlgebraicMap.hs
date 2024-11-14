{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.AlgebraicMap where

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
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Eq

-- | Algebraic map is a much more versatile and powerful tool when used separatey from SpecialSoundProtocol.
-- It calculates a system of equations @[f]@ defining @a@ in some way.
-- If @f@ is a number or a field element, then the result is a vector of polynomial values.
-- However, @f@ can be a polynomial, in which case the result will be a system of polynomials.
-- This polymorphism is exploited in the AccumulatorScheme prover.
--
class AlgebraicMap f i (d :: Natural) a where
    -- | the algebraic map V_sps computed by the verifier.
    algebraicMap :: a
        -> i f            -- ^ public input
        -> Vector k [f]   -- ^ NARK proof witness (the list of prover messages)
        -> Vector (k-1) f -- ^ Verifier random challenges
        -> f              -- ^ Slack variable for padding
        -> [f]

instance
  ( Ring f
  , Representable i
  , KnownNat (d + 1)
  , Arithmetic a
  , Scale a f
  ) => AlgebraicMap f i d (ArithmeticCircuit a i o) where
    -- We can use the polynomial system from the circuit as a base for V_sps.
    --
    algebraicMap ac pi pm _ pad = padDecomposition pad f_sps_uni
        where
            sys :: [PM.Poly a (SysVar i) Natural]
            sys = M.elems (acSystem ac)

            witness :: Map ByteString f
            witness = M.fromList $ zip (keys $ acWitness ac) (V.head pm)

            varMap :: SysVar i -> f
            varMap (InVar inV)   = index pi inV
            varMap (NewVar newV) = M.findWithDefault zero newV witness

            f_sps :: Vector (d+1) [PM.Poly a (SysVar i) Natural]
            f_sps = degreeDecomposition @_ @d $ sys

            f_sps_uni :: Vector (d+1) [f]
            f_sps_uni = fmap (PM.evalPolynomial PM.evalMonomial varMap) <$> f_sps


padDecomposition :: forall f n .
    ( KnownNat n
    , MultiplicativeMonoid f
    , AdditiveMonoid f
     ) => f -> V.Vector n [f] -> [f]
padDecomposition pad = foldl' (P.zipWith (+)) (P.repeat zero) . V.mapWithIx (\j p -> ((pad ^ (d -! j)) * ) <$> p)
    where
        d = value @n -! 1

-- | Decomposes an algebraic map into homogenous degree-j maps for j from 0 to @d@
--
degreeDecomposition :: forall f d v . KnownNat (d + 1) => [Poly f v Natural] -> V.Vector (d + 1) [Poly f v Natural]
degreeDecomposition lmap = tabulate (degree_j . toConstant)
    where
        degree_j :: Natural -> [Poly f v Natural]
        degree_j j = P.fmap (leaveDeg j) lmap

        leaveDeg :: Natural -> PM.Poly f v Natural -> PM.Poly f v Natural
        leaveDeg j (PM.P monomials) = PM.P $ P.filter (\(_, m) -> deg m == j) monomials

deg :: PM.Mono v Natural -> Natural
deg (PM.M m) = sum m
