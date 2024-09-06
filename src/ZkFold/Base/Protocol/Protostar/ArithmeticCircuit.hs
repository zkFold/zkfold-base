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


-- | A data for recurcive computations.
-- @circuit@ is an Arithmetic circuit with @n@ inputs and @n@ outputs applied to itself (i.e. outputs are fed as inputs at the next iteration) @iterations@ times.
--
data RecursiveCircuit n a
    = RecursiveCircuit
        { iterations :: Natural
        , circuit    :: ArithmeticCircuit a (Vector n) (Vector n)
        } deriving (Generic, NFData)

instance (KnownNat n, Arithmetic a, P.Show a) => SPS.SpecialSoundProtocol f (RecursiveCircuit n a) where
    type Witness f (RecursiveCircuit n a) = Map Natural f
    type Input f (RecursiveCircuit n a) = Vector n f
    type ProverMessage f (RecursiveCircuit n a) = Map Natural f
    type VerifierMessage f (RecursiveCircuit n a) = a
    type Degree (RecursiveCircuit n a) = 2

    -- One round for Plonk
    rounds = P.const 1

    outputLength (RecursiveCircuit _ ac) = (P.fromIntegral $ M.size (acSystem ac)) + 1

    -- The transcript will be empty at this point, it is a one-round protocol
    --
    prover rc@(RecursiveCircuit _ ac) _ i _ = witnessGenerator ac i

    -- We can modify the polynomial system from the circuit.
    -- The result is a system of @n+1@-variate polynomials
    -- where variables @0@ to @n-1@ are inputs and variable @n@ is hash of the prover message
    --
    algebraicMap rc@(RecursiveCircuit _ ac) i pm _ mu = result
        where
            witness = P.head pm

            sys :: [Poly a (Var (Vector n)) Natural]
            sys = M.elems (acSystem $ circuit rc)

            paddedSum :: [Poly a (Var (Vector n)) Natural]
            paddedSum = padDecomposition mu . degreeDecomposition @(SPS.Degree (RecursiveCircuit n a)) $ sys

            varMap :: Var (Vector n) -> t
            varMap (InVar iv)  = i V.!! (fromZp iv)
            varMap (NewVar nv) = witness ! nv

            result = fmap (PM.evalPolynomial PM.evalMonomial varMap) paddedSum

    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier rc i pm ts = P.all (== zero) $ SPS.algebraicMap @f rc i pm ts one

padDecomposition
    :: forall mu f v d
    .  Exponent mu Natural
    => Scale mu (Poly f v Natural)
    => KnownNat d
    => Field f
    => P.Eq f
    => P.Ord v
    => mu -> V.Vector d [Poly f v Natural] -> [Poly f v Natural]
padDecomposition mu = foldl' (P.zipWith (+)) (P.repeat zero) . V.mapWithIx (\j p -> (scale (mu ^ (d -! j))) <$> p)
    where
        d = value @d

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
