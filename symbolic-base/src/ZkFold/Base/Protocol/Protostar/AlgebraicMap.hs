{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.Protostar.AlgebraicMap where

import           Data.Functor.Rep                                    (tabulate)
import           Data.List                                           (foldl')
import           Data.Map.Strict                                     (Map, fromList)
import qualified Data.Map.Strict                                     as M
import           GHC.IsList                                          (toList)
import           Prelude                                             (fmap, zip, ($), (++), (.), (<$>))
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
class AlgebraicMap f a where
    type MapInput f a
    type MapMessage f a
    type Degree a :: Natural
    -- ^ d in the paper, the verifier degree

    -- | the algebraic map V_sps computed by the verifier.
    algebraicMap :: a
        -> MapInput f a     -- ^ public input
        -> [MapMessage f a] -- ^ NARK proof witness (the list of prover messages)
        -> [f]              -- ^ Verifier random challenges
        -> f                -- ^ Slack variable for padding
        -> [f]

instance
  ( KnownNat n
  , Arithmetic a
  , Scale a f
  , MultiplicativeMonoid f
  , AdditiveMonoid f
  ) => AlgebraicMap f (ArithmeticCircuit a (Vector n) o) where

    type MapInput f (ArithmeticCircuit a (Vector n) o) = Vector n f
    type MapMessage f (ArithmeticCircuit a (Vector n) o) = [f]
    type Degree (ArithmeticCircuit a (Vector n) o) = 2

    -- We can use the polynomial system from the circuit as a base for V_sps.
    --
    algebraicMap ac pi pm _ pad = padDecomposition pad f_sps_uni
        where
            sys :: [PM.Poly a (SysVar (Vector n)) Natural]
            sys = M.elems (acSystem ac)

            witness :: Map (SysVar (Vector n)) f
            witness = fromList $ zip (getAllVars ac) (toList pi ++ P.head pm)

            varMap :: SysVar (Vector n) -> f
            varMap x = M.findWithDefault zero x witness

            f_sps :: Vector 3 [PM.Poly a (SysVar (Vector n)) Natural]
            f_sps = degreeDecomposition @(Degree (ArithmeticCircuit a (Vector n) o)) $ sys

            f_sps_uni :: Vector 3 [f]
            f_sps_uni = fmap (PM.evalPolynomial PM.evalMonomial varMap) <$> f_sps


padDecomposition
    :: forall f d
    .  KnownNat d
    => MultiplicativeMonoid f
    => AdditiveMonoid f
    => f -> V.Vector d [f] -> [f]
padDecomposition pad = foldl' (P.zipWith (+)) (P.repeat zero) . V.mapWithIx (\j p -> ((pad ^ (d -! j)) * ) <$> p)
    where
        d = value @d -! 1

-- | Decomposes an algebraic map into homogenous degree-j maps for j from 0 to @n@
--
degreeDecomposition :: forall n f v . KnownNat (n + 1) => [Poly f v Natural] -> V.Vector (n + 1) [Poly f v Natural]
degreeDecomposition lmap = tabulate (degree_j . toConstant)
    where
        degree_j :: Natural -> [Poly f v Natural]
        degree_j j = P.fmap (leaveDeg j) lmap

        leaveDeg :: Natural -> PM.Poly f v Natural -> PM.Poly f v Natural
        leaveDeg j (PM.P monomials) = PM.P $ P.filter (\(_, m) -> deg m == j) monomials

deg :: PM.Mono v Natural -> Natural
deg (PM.M m) = sum m