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
import           GHC.Generics                                     (Generic, Par1)
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
import           ZkFold.Symbolic.Data.Class
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
    => FieldElement ctx
    -> C n a
    -> Vector n (FieldElement ctx)
    -> FS_CM ctx n comm a
toFS ck rc v = FiatShamir (CommitOpen (hcommit ck) rc) v

-- No SymbolicData instances for data
-- all protocols are one-round in case of arithmetic circuits, therefore we can replace lists with elements.
ivcVerifier 
    :: forall i f c m ctx a 
    .  Symbolic ctx
    => SymbolicData i
    => SymbolicData f
    => SymbolicData c
    => SymbolicData m
    => SymbolicData a
    => Acc.AccumulatorScheme i f c m ctx a
    => (i, c, (i, c, f, c, f), (i, c, f, c, f), c) 
    -> (a, (f, (f, f)), ((i, c, f, c, f), m)) 
    -> Bool ctx 
ivcVerifier (i, pi_x, accTuple, acc'Tuple, pf) (a, ckTuple, dkTuple) 
  = (Acc.verifier @i @f @c @m @ctx @a i [pi_x] acc acc' [pf]) && (Acc.decider @i @f @c @m @ctx @a a ck dk)
    where
        acc = let (x1, x2, x3, x4, x5) = accTuple
               in AccumulatorInstance x1 [x2] [x3] x4 x5
        acc' = let (x1, x2, x3, x4, x5) = acc'Tuple
                in AccumulatorInstance x1 [x2] [x3] x4 x5

        ck = let (f, (x1, x2)) = ckTuple
              in (f, Acc.KeyScale x1 x2)

        dk = let ((x1, x2, x3, x4, x5), m) = dkTuple
              in Accumulator (AccumulatorInstance x1 [x2] [x3] x4 x5) [m]

ivcVerifierAc
    :: forall i f c m ctx a y
    .  Symbolic ctx
    => Acc.AccumulatorScheme i f c m ctx a
    => y 
ivcVerifierAc = compile (ivcVerifier @i @f @c @m @ctx @a)

iterate
    :: forall ctx n comm a
    .  Symbolic ctx
    => KnownNat n
    => Arithmetic a
    => Scale a (BaseField ctx)
    => FromConstant a (BaseField ctx)
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
    -> Vector n a
    -> Natural
    -> ProtostarResult ctx n comm a
iterate f i0 n = iteration n ck f ac i0_arith i0 initialAccumulator (Acc.KeyScale one one)
    where
        i0_arith :: Vector n (FieldElement ctx)
        i0_arith = fromConstant <$> i0

        ac :: C n a
        ac = compile @a f

        initE = hcommit ck $ replicate (SPS.outputLength @(FieldElement ctx) ac) (zero :: FieldElement ctx)

        ck :: FieldElement ctx
        ck = oracle i0_arith

        initialAccumulator :: Acc ctx n comm a
        initialAccumulator = Accumulator (AccumulatorInstance (P.pure zero) [hcommit ck [zero :: SPS.MapMessage (FieldElement ctx) (C n a)]] [] initE zero) [zero]

instanceProof
    :: forall ctx n comm a
    .  Symbolic ctx
    => Arithmetic a
    => Scale a (BaseField ctx)
    => FromConstant a (BaseField ctx)
    => HomomorphicCommit (FieldElement ctx) [SPS.MapMessage (FieldElement ctx) (C n a)] comm
    => FieldElement ctx
    -> C n a
    -> SPS.MapInput (FieldElement ctx) (C n a)
    -> Vector n a 
    -> InstanceProofPair (Vector n (FieldElement ctx)) comm (SPS.MapMessage (FieldElement ctx) (C n a))
instanceProof ck rc i i_pure = InstanceProofPair i (NARKProof [hcommit ck [m]] [m])
    where
        m = SPS.prover @(FieldElement ctx) rc (i_pure, M.empty) i []

iteration
    :: forall ctx n comm a
    .  Symbolic ctx
    => KnownNat n
    => Arithmetic a
    => Scale a (BaseField ctx)
    => FromConstant a (BaseField ctx)
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
    -> Vector n a
    -> Acc ctx n comm a
    -> Acc.KeyScale (FieldElement ctx)
    -> ProtostarResult ctx n comm a
iteration 0 _  _ _  i _ acc _  = ProtostarResult i acc
iteration n ck f rc i i_pure acc (Acc.KeyScale alphaSum muSum) = iteration (n -! 1) ck f rc newi newi_pure newAcc newKS
    where
        fs :: FS_CM ctx n comm a
        fs = toFS ck rc i

        nark@(InstanceProofPair _ narkProof) = instanceProof @ctx @n @comm @a ck rc i i_pure
        (newAcc, accProof) = Acc.prover @_ @(FieldElement ctx) @comm @_ @ctx fs ck acc nark

        alpha :: FieldElement ctx
        alpha = oracle (acc^.x, i, narkCommits narkProof, accProof)

        alphaPows = sum $ P.take (P.length accProof) $ (alpha ^) <$> [1 :: Natural ..]

        newi = f i

        newi_pure = eval rc i_pure

        newKS = Acc.KeyScale (alphaSum + alphaPows) (muSum + scale (6 :: Natural) alpha)
