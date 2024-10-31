{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Base.Protocol.Protostar.Fold where


import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           Data.Binary                                      (Binary)
import           Data.Function                                    ((.))
import           Data.Functor                                     (fmap)
import           Data.Kind                                        (Type)
import           Data.Map.Strict                                  (Map)
import qualified Data.Map.Strict                                  as M
import           Data.Proxy                                       (Proxy)
import           GHC.Generics                                     (Generic, Par1 (..), U1 (..), type (:*:) (..),
                                                                   type (:.:) (..))
import           Prelude                                          (type (~), ($), (<$>), (<*>))
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate       as PU
import           ZkFold.Base.Data.HFunctor                        (hmap)
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
import           ZkFold.Symbolic.Data.Input                       (SymbolicInput)
import ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol(..))


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
    linearCombination mx ma = (+) . P.flip PU.polyVecLinear zero <$> mx <*> (PU.polyVecConstant <$> ma)

instance (Ring a, KnownNat n) => Acc.LinearCombinationWith a (Vector n a) where
    linearCombinationWith coeff a b = (+) <$> P.fmap (coeff *) a <*> b


-- type C n a = ArithmeticCircuit a (Vector n) (Vector n)
-- type FS_CM ctx n comm a = FiatShamir (FieldElement ctx) (CommitOpen (SPS.MapMessage (FieldElement ctx) (C n a)) comm (C n a))
-- type Acc ctx n comm a = Accumulator (Vector n (FieldElement ctx)) (FieldElement ctx) comm (SPS.MapMessage (FieldElement ctx) (C n a))

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data ProtostarResult pi f c m
    = ProtostarResult
    { result           :: pi
    , finalAccumulator :: Accumulator pi f c m
    , finalAccProof    :: [c]
    } deriving (Generic)

deriving instance (NFData pi, NFData f, NFData c, NFData m) => NFData (ProtostarResult pi f c m)
deriving instance (P.Show pi, P.Show f, P.Show c, P.Show m) => P.Show (ProtostarResult pi f c m)

toFS
    :: forall pi f c m
    .  HomomorphicCommit f [m] c
    => Input f (pi -> pi) ~ pi
    => f
    -> (pi -> pi)
    -> FiatShamir f (CommitOpen m c (pi -> pi))
toFS ck func = FiatShamir (CommitOpen (hcommit ck) func)

-- No SymbolicData instances for data
-- all protocols are one-round in case of arithmetic circuits, therefore we can replace lists with elements.
-- TODO: upgrade to the multi-round version
ivcVerifier
    :: forall pi f c m a
    .  Acc.AccumulatorScheme pi f c m a
    => (pi, c, (pi, c, f, c, f), (pi, c, f, c, f), c)
    -> (a, (f, (f, f)), ((pi, c, f, c, f), m))
    -> ((f, pi, [f], [c], c), ([c], c))
ivcVerifier (i, pi_x, accTuple, acc'Tuple, pf) (a, ckTuple, dkTuple)
  = (Acc.verifier @pi @f @c @m @a i [pi_x] acc acc' [pf], Acc.decider @pi @f @c @m @a a ck dk)
    where
        acc = let (x1, x2, x3, x4, x5) = accTuple
               in AccumulatorInstance x1 [x2] [x3] x4 x5
        acc' = let (x1, x2, x3, x4, x5) = acc'Tuple
                in AccumulatorInstance x1 [x2] [x3] x4 x5

        ck = let (f, (x1, x2)) = ckTuple
              in (f, Acc.KeyScale x1 x2)

        dk = let ((x1, x2, x3, x4, x5), m) = dkTuple
              in Accumulator (AccumulatorInstance x1 [x2] [x3] x4 x5) [m]

-- -- TODO: this is insane
-- ivcVerifierAc
--     :: forall i f c m ctx a y t
--     .  Symbolic ctx
--     => SymbolicInput (i, c, (i, c, f, c, f), (i, c, f, c, f), c)
--     => SymbolicInput (a, (f, (f, f)), ((i, c, f, c, f), m))
--     => SymbolicData y
--     => Context a ~ ctx
--     => Context i ~ ctx
--     => Context y ~ ctx
--     => Support y ~ Proxy ctx
--     => Layout y ~ Par1
--     => t ~ ((i,c,(i,c,f,c,f),(i,c,f,c,f),c),(a,(f,f,f),(i,c,f,c,f),m),Proxy ctx)
--     => ctx ~ ArithmeticCircuit a (Layout t)
--     => Acc.AccumulatorScheme i f c m a
--     => y
-- ivcVerifierAc = compile (ivcVerifier @i @f @c @m @a)

-- iterate
--     :: forall ctx n comm a
--     .  KnownNat n
--     => Arithmetic a
--     => Binary a
--     => Scale a (BaseField ctx)
--     => FromConstant a (BaseField ctx)
--     => Eq (Bool ctx) comm
--     => Eq (Bool ctx) [comm]
--     => Eq (Bool ctx) [FieldElement ctx]
--     => Eq (Bool ctx) (Vector n (FieldElement ctx))
--     => RandomOracle comm (FieldElement ctx)
--     => HomomorphicCommit (FieldElement ctx) [FieldElement ctx] comm
--     => HomomorphicCommit (FieldElement ctx) [SPS.MapMessage (FieldElement ctx) (C n a)] comm
--     => AdditiveGroup comm
--     => Scale a (PU.PolyVec (FieldElement ctx) 3)
--     => Scale a (FieldElement ctx)
--     => Scale (FieldElement ctx) comm
--     => ctx ~ ArithmeticCircuit a (Vector n)
--     => SPS.Input (FieldElement ctx) (C n a) ~ Vector n (FieldElement ctx)
--     => (forall c. (Symbolic c, BaseField c ~ a) => Vector n (FieldElement c) -> Vector n (FieldElement c))
--     -> Vector n a
--     -> Natural
--     -> ProtostarResult ctx n comm a
-- iterate f i0 n = iteration n ck f ac i0_arith i0 initialAccumulator (Acc.KeyScale one one)
--     where
--         i0_arith :: Vector n (FieldElement ctx)
--         i0_arith = fromConstant <$> i0

--         ac :: C n a
--         ac = hmap (fmap unPar1 . unComp1) $ hlmap ((:*: U1) . Comp1 . fmap Par1) (compile @a f)

--         initE = hcommit ck $ replicate (SPS.outputLength @(FieldElement ctx) ac) (zero :: FieldElement ctx)

--         ck :: FieldElement ctx
--         ck = oracle i0_arith

--         initialAccumulator :: Acc ctx n comm a
--         initialAccumulator = Accumulator (AccumulatorInstance (P.pure zero) [hcommit ck [zero :: SPS.MapMessage (FieldElement ctx) (C n a)]] [] initE zero) [zero]

instanceProof
    :: forall pi f c m
    .  AdditiveMonoid f
    => HomomorphicCommit f [m] c
    => SpecialSoundProtocol f (pi -> pi)
    => Witness f (pi -> pi) ~ ()
    => Input f (pi -> pi) ~ pi
    => ProverMessage f (pi -> pi) ~ m
    => f
    -> (pi -> pi)
    -> pi
    -> InstanceProofPair pi c m
instanceProof ck func i = InstanceProofPair i (NARKProof [hcommit ck [m]] [m])
    where
        -- TODO: here we are using `zero` as the transcript
        m = SPS.prover @f func () i zero

iteration
    :: forall pi f c m
    .  RandomOracle pi f
    => RandomOracle c f
    => Acc.LinearCombination m (SPS.MapMessage (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi))
    => Acc.LinearCombination pi (SPS.MapInput (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi))
    => Acc.LinearCombinationWith f pi
    => SPS.AlgebraicMap f (pi -> pi)
    => SPS.AlgebraicMap (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi)
    => HomomorphicCommit f [f] c
    => HomomorphicCommit f [m] c
    => AdditiveGroup pi
    => AdditiveGroup c
    => AdditiveSemigroup m
    => SpecialSoundProtocol f (pi -> pi)
    => KnownNat (Degree (pi -> pi) + 1)
    => Witness f (pi -> pi) ~ ()
    => Input f (pi -> pi) ~ pi
    => ProverMessage f (pi -> pi) ~ m
    => SPS.MapInput f (pi -> pi) ~ pi
    => SPS.MapMessage f (pi -> pi) ~ m
    => Scale f (PU.PolyVec f 3)
    => Scale f c
    => Scale f m
    => Ring f
    => Natural
    -> f
    -> (pi -> pi)
    -> ProtostarResult pi f c m
    -> ProtostarResult pi f c m
iteration 0 _  _     res = res
iteration n ck func (ProtostarResult i acc _) = iteration (n -! 1) ck func (ProtostarResult newi newAcc accProof)
    where
        fs :: FiatShamir f (CommitOpen m c (pi -> pi))
        fs = toFS ck func

        newi = func i

        nark = instanceProof ck func i
        (newAcc, accProof) = Acc.prover @pi @f @c @m fs ck acc nark
