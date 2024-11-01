{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Base.Protocol.Protostar.Fold where


import           Control.DeepSeq                                  (NFData)
import           Data.Proxy                                       (Proxy)
import           GHC.Generics                                     (Generic, Par1)
import           GHC.IsList                                       (IsList (..))
import           Prelude                                          (head, type (~), ($))
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate       as PU
import           ZkFold.Base.Protocol.Protostar.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.Protostar.ArithmeticCircuit ()
import           ZkFold.Base.Protocol.Protostar.Commit
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.Oracle
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound      as SPS
import           ZkFold.Base.Protocol.Protostar.SpecialSound      (AlgebraicMap (..), SpecialSoundProtocol (..))
import           ZkFold.Prelude                                   (replicate)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Input                       (SymbolicInput)

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data ProtostarResult pi f c m
    = ProtostarResult
    { result           :: pi
    , finalAccumulator :: Accumulator pi f c m
    , finalAccProof    :: [c]
    } deriving (GHC.Generics.Generic)

deriving instance (NFData pi, NFData f, NFData c, NFData m) => NFData (ProtostarResult pi f c m)
deriving instance (P.Show pi, P.Show f, P.Show c, P.Show m) => P.Show (ProtostarResult pi f c m)

toFS
    :: forall pi f c m
    .  HomomorphicCommit f m c
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
    -> (a, f, ((pi, c, f, c, f), m))
    -> ((f, pi, f, c, c), (c, c))
ivcVerifier (i, pi_x, accTuple, acc'Tuple, pf) (a, ck, dkTuple)
  = (verifierResult, deciderResult)
    where
        acc = let (x1, x2, x3, x4, x5) = accTuple
               in AccumulatorInstance x1 [x2] [x3] x4 x5
        acc' = let (x1, x2, x3, x4, x5) = acc'Tuple
                in AccumulatorInstance x1 [x2] [x3] x4 x5

        dk = let ((x1, x2, x3, x4, x5), m) = dkTuple
              in Accumulator (AccumulatorInstance x1 [x2] [x3] x4 x5) [m]

        verifierResult =
            let (x1, x2, x3, x4, x5) = Acc.verifier @pi @f @c @m @a i [pi_x] acc acc' [pf]
            in (x1, x2, head x3, head x4, x5)

        deciderResult =
            let (x1, x2) = Acc.decider @pi @f @c @m @a a ck dk
            in (head x1, x2)

ivcVerifier0
    :: forall pi f c m a ctx
    .  Symbolic ctx
    => AdditiveMonoid pi
    => AdditiveMonoid f
    => AdditiveMonoid c
    => Eq (Bool ctx) pi
    => Eq (Bool ctx) f
    => Eq (Bool ctx) c
    => Acc.AccumulatorScheme pi f c m a
    => (pi, c, (pi, c, f, c, f), (pi, c, f, c, f), c)
    -> (a, f, ((pi, c, f, c, f), m))
    -> Bool ctx
ivcVerifier0 arg1 arg2 =
    let ((x1, x2, x3, x4, x5), (x6, x7)) = ivcVerifier @pi @f @c @m @a arg1 arg2
    in x1 == zero && x2 == zero && x3 == zero && x4 == zero && x5 == zero && x6 == zero && x7 == zero

-- TODO: this is insane
ivcVerifierAc
    :: forall pi f c m ctx a y t
    .  Symbolic ctx
    => AdditiveMonoid pi
    => AdditiveMonoid f
    => AdditiveMonoid c
    => Eq (Bool ctx) pi
    => Eq (Bool ctx) f
    => Eq (Bool ctx) c
    => SymbolicInput (pi, c, (pi, c, f, c, f), (pi, c, f, c, f), c)
    => SymbolicInput (a, f, ((pi, c, f, c, f), m))
    => SymbolicData y
    => Context a ~ ctx
    => Context pi ~ ctx
    => Context y ~ ctx
    => Support y ~ Proxy ctx
    => Layout y ~ GHC.Generics.Par1
    => t ~ ((pi,c,(pi,c,f,c,f),(pi,c,f,c,f),c),(a,f,(pi,c,f,c,f),m),Proxy ctx)
    => ctx ~ ArithmeticCircuit a (Layout t)
    => Acc.AccumulatorScheme pi f c m a
    => y
ivcVerifierAc = compile (ivcVerifier0 @pi @f @c @m @a)

iterate
    :: forall pi f c m
    .  AdditiveGroup pi
    => AdditiveGroup c
    => AdditiveMonoid m
    => Ring f
    => Scale f pi
    => Scale f c
    => Scale f m
    => RandomOracle pi f
    => RandomOracle c f
    => HomomorphicCommit f [f] c
    => HomomorphicCommit f m c
    => IsList pi
    => Item pi ~ f
    => IsList m
    => Item m ~ f
    => AlgebraicMap f (pi -> pi)
    => MapInput f (pi -> pi) ~ pi
    => MapMessage f (pi -> pi) ~ m
    => AlgebraicMap (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi)
    => MapInput (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi) ~ [PU.PolyVec f (Degree (pi -> pi) + 1)]
    => MapMessage (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi) ~ PU.PolyVec f (Degree (pi -> pi) + 1)
    => SpecialSoundProtocol f (pi -> pi)
    => KnownNat (Degree (pi -> pi) + 1)
    => Witness f (pi -> pi) ~ ()
    => Input f (pi -> pi) ~ pi
    => ProverMessage f (pi -> pi) ~ m
    =>  (pi -> pi)
    -> pi
    -> Natural
    -> ProtostarResult pi f c m
iterate func pi n = iteration n ck func initialResult
    where
        initE = hcommit ck $ replicate (outputLength @f func) (zero :: f)

        ck :: f
        ck = oracle pi

        initialAccumulator :: Accumulator pi f c m
        initialAccumulator = Accumulator (AccumulatorInstance zero (P.map (P.const zero) [1.. rounds @f func]) (P.map (P.const zero) [1 .. rounds @f func]) initE zero) [zero]

        initialResult :: ProtostarResult pi f c m
        initialResult = ProtostarResult pi initialAccumulator []

instanceProof
    :: forall pi f c m
    .  RandomOracle pi f
    => HomomorphicCommit f m c
    => SpecialSoundProtocol f (pi -> pi)
    => Witness f (pi -> pi) ~ ()
    => Input f (pi -> pi) ~ pi
    => ProverMessage f (pi -> pi) ~ m
    => f
    -> (pi -> pi)
    -> pi
    -> InstanceProofPair pi c m
instanceProof ck func pi = InstanceProofPair pi (NARKProof [hcommit ck m] [m])
    where
        m = SPS.prover @f func () pi (oracle pi) 0

iteration
    :: forall pi f c m
    .  AdditiveGroup pi
    => AdditiveGroup c
    => AdditiveSemigroup m
    => Ring f
    => Scale f pi
    => Scale f c
    => Scale f m
    => RandomOracle pi f
    => RandomOracle c f
    => HomomorphicCommit f [f] c
    => HomomorphicCommit f m c
    => IsList pi
    => Item pi ~ f
    => IsList m
    => Item m ~ f
    => AlgebraicMap f (pi -> pi)
    => MapInput f (pi -> pi) ~ pi
    => MapMessage f (pi -> pi) ~ m
    => AlgebraicMap (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi)
    => MapInput (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi) ~ [PU.PolyVec f (Degree (pi -> pi) + 1)]
    => MapMessage (PU.PolyVec f (Degree (pi -> pi) + 1)) (pi -> pi) ~ PU.PolyVec f (Degree (pi -> pi) + 1)
    => SpecialSoundProtocol f (pi -> pi)
    => KnownNat (Degree (pi -> pi) + 1)
    => Witness f (pi -> pi) ~ ()
    => Input f (pi -> pi) ~ pi
    => ProverMessage f (pi -> pi) ~ m
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
