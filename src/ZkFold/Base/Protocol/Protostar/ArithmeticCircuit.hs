{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.ArithmeticCircuit where


import           Control.DeepSeq                                     (NFData)
import           Control.Lens                                        ((^.))
import           Data.List                                           (foldl')
import           Data.Map.Strict                                     (Map, (!))
import qualified Data.Map.Strict                                     as M
import           Debug.Trace
import           GHC.Generics                                        (Generic)
import           Prelude                                             (and, fmap, otherwise, type (~), ($), (.), (<$>),
                                                                      (<), (<=), (<>), (==))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate        as PM
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import qualified ZkFold.Base.Algebra.Polynomials.Univariate          as PU
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.Protostar.Accumulator
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme    as Acc
import           ZkFold.Base.Protocol.Protostar.Commit
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.Oracle
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound         as SPS
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Combinators                    (Iso (..))
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement)

{--

1. Compress verification checks (Section 3.5; )
2. Commit (Section 3.2; ZkFold.Base.Protocol.ARK.Protostar.CommitOpen)
3. Fiat-Shamir transform (Section 3.3; ZkFold.Base.Protocol.ARK.Protostar.FiatShamir)
   A technique for taking an interactive proof of knowledge and creating a digital signature based on it.
   This way, some fact (for example, knowledge of a certain secret number) can be publicly proven without revealing underlying information.
4. Accumulation scheme (Section 3.4; ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme)
5. Obtain the IVC scheme (Theorem 1 from “Proof-Carrying Data Without Succinct Arguments”; )

--}


-- | A type for recurcive computations.
-- @circuit@ is an Arithmetic circuit with @n@ inputs and @n@ outputs applied to itself (i.e. outputs are fed as inputs at the next iteration) @iterations@ times.
--
data RecursiveCircuit n a
    = RecursiveCircuit
        { iterations :: Natural
        , circuit    :: ArithmeticCircuit a (Vector n) (Vector n)
        } deriving (Generic, NFData)

instance (Ring f, P.Eq f) => Iso (PU.Poly f) f where
    from = P.flip PU.evalPoly zero

instance (Ring f, P.Eq f) => Iso f (PU.Poly f) where
    from = PU.constant

instance Iso a a where
    from = P.id

instance
  ( KnownNat n
  , Arithmetic a
  , P.Eq f
  , Scale a f
  , MultiplicativeMonoid f
  , Exponent f Natural
  , AdditiveMonoid f
  , Iso a f
  ) => SPS.SpecialSoundProtocol f (RecursiveCircuit n a) where

    type Witness f (RecursiveCircuit n a) = Map Natural a
    type Input f (RecursiveCircuit n a) = Vector n f
    type ProverMessage f (RecursiveCircuit n a) = Map Natural f
    type VerifierMessage f (RecursiveCircuit n a) = a
    type Degree (RecursiveCircuit n a) = 2

    -- One round for Plonk
    rounds = P.const 1

    outputLength (RecursiveCircuit _ ac) = (P.fromIntegral $ M.size (acSystem ac)) + 1

    -- The transcript will be empty at this point, it is a one-round protocol
    --
    prover rc@(RecursiveCircuit _ ac) _ i _ = from @a <$> witnessGenerator ac (from @f <$> i)

    -- We can use thepolynomial system from the xircuit as a base for V_sps.
    --
    algebraicMap rc@(RecursiveCircuit _ ac) i pm _ mu = padDecomposition mu f_sps_uni
        where
            witness = P.head pm

            sys :: [PM.Poly a (Var (Vector n)) Natural]
            sys = M.elems (acSystem ac)

            varMap :: Var (Vector n) -> f
            varMap (InVar iv)  = i V.!! (fromZp iv)
            varMap (NewVar nv) = M.findWithDefault zero nv witness

            f_sps :: Vector 3 [PM.Poly a (Var (Vector n)) Natural]
            f_sps = degreeDecomposition @(SPS.Degree (RecursiveCircuit n a)) $ sys

            f_sps_uni :: Vector 3 [f]
            f_sps_uni = fmap (PM.evalPolynomial PM.evalMonomial varMap) <$> f_sps


    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier rc i pm ts = P.all (== zero) $ SPS.algebraicMap @f rc i pm ts one

padDecomposition
    :: forall f d
    .  KnownNat d
    => MultiplicativeSemigroup f
    => Exponent f Natural
    => AdditiveMonoid f
    => f -> V.Vector d [f] -> [f]
padDecomposition mu = foldl' (P.zipWith (+)) (P.repeat zero) . V.mapWithIx (\j p -> ((mu ^ (d -! j)) * ) <$> p)
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
