{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Base.Protocol.Protostar.Fold where


import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           Data.Kind                                        (Type)
import           Data.Map.Strict                                  (Map)
import qualified Data.Map.Strict                                  as M
import           GHC.Generics                                     (Generic, Par1, U1)
import           Prelude                                          (type (~), ($), (<$>), (<*>))
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate       as PU
import           ZkFold.Base.Data.Vector                          (Vector)
import           ZkFold.Base.Protocol.Protostar.Accumulator
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.Protostar.ArithmeticCircuit ()
import           ZkFold.Base.Protocol.Protostar.Commit
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.Oracle
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound      as SPS
import           ZkFold.Prelude                                   (replicate)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement                (FieldElement)


-- | These instances might seem off, but accumulator scheme requires this exact behaviour for ProverMessages which are Maps in this case.
--
instance Scale s a => Scale s (Map k a) where
    scale s = P.fmap (scale s)

instance (AdditiveSemigroup a, P.Ord key) => AdditiveSemigroup (Map key a) where
    (+) = M.unionWith (+)

instance (AdditiveMonoid a, P.Ord key) => AdditiveMonoid (Map key a) where
    zero = M.empty

instance (Ring a, P.Ord key, KnownNat k) => Acc.LinearCombination (Map key a) (Map key (PU.PolyVec a k)) where
    linearCombination mx ma = M.unionWith (+) (P.flip PU.polyVecLinear zero <$> mx) (PU.polyVecConstant <$> ma)

instance (Ring a, KnownNat n, KnownNat k) => Acc.LinearCombination (Vector n a) (Vector n (PU.PolyVec a k)) where
    linearCombination mx ma = (+) <$> (P.flip PU.polyVecLinear zero <$> mx) <*> (PU.polyVecConstant <$> ma)

instance (Ring a, KnownNat n) => Acc.LinearCombinationWith a (Vector n a) where
    linearCombinationWith coeff a b = (+) <$> (P.fmap (coeff *) a) <*> b


type C n a = ArithmeticCircuit a (Vector n) (Vector n)
type FS_CM ctx n comm a = FiatShamir (FieldElement ctx) (CommitOpen (SPS.MapMessage (FieldElement ctx) (C n a)) comm (C n a))
type Acc ctx n comm a = Accumulator (Vector n (FieldElement ctx)) (FieldElement ctx) comm (SPS.MapMessage (FieldElement ctx) (C n a))

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data ProtostarResult (ctx :: (Type -> Type) -> Type) n comm a
    = ProtostarResult
    { result       :: Vector n (FieldElement ctx)
    , proverOutput :: Acc ctx n comm a
    } deriving (Generic)

deriving instance (NFData (Bool ctx), NFData comm, NFData (FieldElement ctx)) => NFData (ProtostarResult ctx n comm a)
deriving instance (P.Show (Bool ctx), P.Show comm, P.Show (ctx Par1)) => P.Show (ProtostarResult ctx n comm a)

toFS
    :: forall ctx n comm a
    .  HomomorphicCommit (FieldElement ctx) [SPS.MapMessage (FieldElement ctx) (C n a)] comm
    => SPS.Input (FieldElement ctx) (C n a) ~ Vector n (FieldElement ctx)
    => FieldElement ctx
    -> C n a
    -> Vector n (FieldElement ctx)
    -> FS_CM ctx n comm a
toFS ck rc v = FiatShamir (CommitOpen (hcommit ck) rc) v

iterate
    :: forall ctx n comm a
    .  Symbolic ctx
    => KnownNat n
    => Arithmetic a
    => Eq (Bool ctx) comm
    => Eq (Bool ctx) [comm]
    => Eq (Bool ctx) [FieldElement ctx]
    => Eq (Bool ctx) (Vector n (FieldElement ctx))
    => RandomOracle comm (FieldElement ctx)
    => HomomorphicCommit (FieldElement ctx) [FieldElement ctx] comm
    => HomomorphicCommit (FieldElement ctx) [SPS.MapMessage (FieldElement ctx) (C n a)] comm
    => AdditiveGroup comm
    => Scale a (PU.PolyVec (FieldElement ctx) 3)
    => Scale a (FieldElement ctx)
    => Scale (FieldElement ctx) comm
    => ctx ~ ArithmeticCircuit a (Vector n)
    => SPS.Input (FieldElement ctx) (C n a) ~ Vector n (FieldElement ctx)
    => (Vector n (FieldElement ctx) -> Vector n (FieldElement ctx))
    -> Vector n (FieldElement ctx)
    -> Natural
    -> ProtostarResult ctx n comm a
iterate f i0 n = iteration n ck f ac i0 initialAccumulator (Acc.KeyScale one one)
    where
        ac :: C n a
        ac = compile @a f

        initE = hcommit ck $ replicate (SPS.outputLength @a ac) (zero :: FieldElement ctx)

        ck :: FieldElement ctx
        ck = oracle i0

        initialAccumulator :: Acc ctx n comm a
        initialAccumulator = Accumulator (AccumulatorInstance (P.pure zero) [hcommit ck [zero :: SPS.MapMessage (FieldElement ctx) (C n a)]] [] initE zero) [zero]

instanceProof
    :: forall ctx n comm a
    .  Arithmetic a
    => HomomorphicCommit (FieldElement ctx) [SPS.MapMessage (FieldElement ctx) (C n a)] comm
    => FromConstant a (FieldElement ctx)
    => FieldElement ctx
    -> C n a
    -> SPS.MapInput (FieldElement ctx) (C n a)
    -> InstanceProofPair (Vector n (FieldElement ctx)) comm (SPS.MapMessage (FieldElement ctx) (C n a))
instanceProof ck rc i = InstanceProofPair i (NARKProof [hcommit ck [m]] [m])
    where
        circuitI :: ArithmeticCircuit a U1 (Vector n)
        circuitI = P.undefined

        vecI = exec circuitI

        m = fromConstant <$> SPS.prover @a rc M.empty vecI []

iteration
    :: forall ctx n comm a
    .  Symbolic ctx
    => KnownNat n
    => Arithmetic a
    => FromConstant a (FieldElement ctx)
    => SPS.Input (FieldElement ctx) (C n a) ~ Vector n (FieldElement ctx)
    => Eq (Bool ctx) comm
    => Eq (Bool ctx) [comm]
    => Eq (Bool ctx) [FieldElement ctx]
    => Eq (Bool ctx) (Vector n (FieldElement ctx))
    => RandomOracle comm (FieldElement ctx)
    => HomomorphicCommit (FieldElement ctx) [FieldElement ctx] comm
    => HomomorphicCommit (FieldElement ctx) [SPS.MapMessage (FieldElement ctx) (C n a)] comm
    => AdditiveGroup comm
    => Scale a (PU.PolyVec (FieldElement ctx) 3)
    => Scale a (FieldElement ctx)
    => Scale (FieldElement ctx) comm
    => Natural
    -> FieldElement ctx
    -> (Vector n (FieldElement ctx) -> Vector n (FieldElement ctx))
    -> C n a
    -> SPS.MapInput (FieldElement ctx) (C n a)
    -> Acc ctx n comm a
    -> Acc.KeyScale (FieldElement ctx)
    -> ProtostarResult ctx n comm a
iteration 0 _  _ _  i acc _  = ProtostarResult i acc
iteration n ck f rc i acc (Acc.KeyScale alphaSum muSum) = iteration (n -! 1) ck f rc newi newAcc newKS
    where
        fs :: FS_CM ctx n comm a
        fs = toFS ck rc i

        nark@(InstanceProofPair _ narkProof) = instanceProof @ctx @n @comm @a ck rc i
        (newAcc, accProof) = Acc.prover @_ @(FieldElement ctx) @comm @_ @ctx fs ck acc nark

        alpha :: FieldElement ctx
        alpha = oracle (acc^.x, i, narkCommits narkProof, accProof)

        alphaPows = sum $ P.take (P.length accProof) $ (alpha ^) <$> [1 :: Natural ..]

        newi = f i

        newKS = Acc.KeyScale (alphaSum + alphaPows) (muSum + scale (6 :: Natural) alpha)
