{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE DeriveAnyClass          #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Base.Protocol.Protostar.ArithmeticCircuit where


import           Data.ByteString                                     (ByteString)
import           Data.List                                           (foldl')
import           Data.Map.Strict                                     (Map)
import qualified Data.Map.Strict                                     as M
import           Prelude                                             (fmap, ($), (.), (<$>), (==))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate        as PM
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound         as SPS
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

-- Note:
-- This instance should work when f ~ a and f ~ PU.PolyVec a size
-- Separate instances are not possible because of conflicting associated type family definitions (a is strictly more general than PU.PolyVec a 3)
-- algebraicMap is general enough to deal with both cases
-- However, prover requires an input with @a@ inside to be able to calculate witness.
-- Witness, on the other hand, is a @Map ByteString a@, but prover is expected to return @Map ByteString f@
-- Therefore, we need to provide some kind of transformation between @a@ and @f@, hence the use of @Transform@
--
instance
  ( Arithmetic a
  , Scale a a
  , MultiplicativeMonoid a
  , Exponent a Natural
  , AdditiveMonoid a
  ) => SPS.SpecialSoundProtocol a (ArithmeticCircuit a (Vector n) o) where

    type Witness a (ArithmeticCircuit a (Vector n) o) = Map ByteString a
    type Input a (ArithmeticCircuit a (Vector n) o) = Vector n a
    type ProverMessage a (ArithmeticCircuit a (Vector n) o) = Map ByteString a
    type VerifierMessage a (ArithmeticCircuit a (Vector n) o) = a
    type Degree (ArithmeticCircuit a (Vector n) o) = 2

    -- One round for Plonk
    rounds = P.const 1

    outputLength ac = (P.fromIntegral $ M.size (acSystem ac))

    -- The transcript will be empty at this point, it is a one-round protocol
    --
    prover ac _ i _ = witnessGenerator ac i

    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier rc i pm ts = P.all (== zero) $ SPS.algebraicMap @a rc i pm ts one

instance
  ( Arithmetic a
  , Scale a f
  , MultiplicativeMonoid f
  , Exponent f Natural
  , AdditiveMonoid f
  ) => SPS.AlgebraicMap f (ArithmeticCircuit a (Vector n) o) where

    type MapInput f (ArithmeticCircuit a (Vector n) o) = Vector n f
    type MapMessage f (ArithmeticCircuit a (Vector n) o) = Map ByteString f

    -- We can use the polynomial system from the xircuit as a base for V_sps.
    --
    algebraicMap ac i pm _ pad = padDecomposition pad f_sps_uni
        where
            witness = P.head pm

            sys :: [PM.Poly a (SysVar (Vector n)) Natural]
            sys = M.elems (acSystem ac)

            varMap :: SysVar (Vector n) -> f
            varMap (InVar iv)  = i V.!! (fromZp iv)
            varMap (NewVar nv) = M.findWithDefault zero nv witness

            f_sps :: Vector 3 [PM.Poly a (SysVar (Vector n)) Natural]
            f_sps = degreeDecomposition @(SPS.Degree (ArithmeticCircuit a (Vector n) o)) $ sys

            f_sps_uni :: Vector 3 [f]
            f_sps_uni = fmap (PM.evalPolynomial PM.evalMonomial varMap) <$> f_sps


padDecomposition
    :: forall f d
    .  KnownNat d
    => MultiplicativeSemigroup f
    => Exponent f Natural
    => AdditiveMonoid f
    => f -> V.Vector d [f] -> [f]
padDecomposition pad = foldl' (P.zipWith (+)) (P.repeat zero) . V.mapWithIx (\j p -> ((pad ^ (d -! j)) * ) <$> p)
    where
        d = value @d -! 1

-- | Decomposes an algebraic map into homogenous degree-j maps for j from 0 to @n@
--
degreeDecomposition :: forall n f v . KnownNat (n + 1) => [Poly f v Natural] -> V.Vector (n + 1) [Poly f v Natural]
degreeDecomposition lmap = V.generate degree_j
    where
        degree_j :: Natural -> [Poly f v Natural]
        degree_j j = P.fmap (leaveDeg j) lmap

        leaveDeg :: Natural -> PM.Poly f v Natural -> PM.Poly f v Natural
        leaveDeg j (PM.P monomials) = PM.P $ P.filter (\(_, m) -> deg m == j) monomials

deg :: PM.Mono v Natural -> Natural
deg (PM.M m) = sum m
