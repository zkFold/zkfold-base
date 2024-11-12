{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.Protostar.RecursiveCircuit where

import           Data.Functor.Rep                           (tabulate)
import           Data.Typeable                              (Proxy)
import           GHC.Generics                               (Par1 (..), U1 (..), type (:.:) (..), (:*:) (..))
import           GHC.IsList                                 (IsList (..))
import           Prelude                                    hiding (Num (..), drop, head, take, zipWith)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat)
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Data.HFunctor                  (hmap)
import           ZkFold.Base.Data.Vector                    (Vector, head)
import           ZkFold.Base.Protocol.Protostar.Commit      (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen  (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir  (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.IVC         (IVCInstanceProof, ivcVerify')
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Class                 (SymbolicData (..))
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (..))
import           ZkFold.Symbolic.Data.Input                 (SymbolicInput)

-- | Takes a function `f` and returns a circuit `C` with input `y` and witness `w`.
-- The circuit is such that `C(y, w) = 0` implies that `y = x(n)` for some positive `n` where
-- `x(k+1) = f(x(k), u(k))` for all `k` and some `u`.
protostar :: forall a n k i o ctx f pi m c .
    ( Binary a
    , Arithmetic a
    , KnownNat n
    , KnownNat k
    , ctx ~ ArithmeticCircuit a i
    , f ~ FieldElement ctx
    , pi ~ Vector n f
    , m ~ [f]
    , c ~ f
    , SymbolicInput (IVCInstanceProof pi f c m)
    , Context (IVCInstanceProof pi f c m) ~ ctx
    , HomomorphicCommit m c
    , i ~ Layout (IVCInstanceProof pi f c m) :*: U1
    , o ~ (((Par1 :*: (Vector n :.: Par1)) :*: (Par1 :*: (Par1 :*: Par1))) :*: (Par1 :*: Par1))
    ) => (forall ctx' . Symbolic ctx' => Vector n (FieldElement ctx') -> Vector k (FieldElement ctx') -> Vector n (FieldElement ctx'))
    -> ArithmeticCircuit a i o
protostar func =
    let
        -- The step function for the recursion: `F(x, u, y) = f(x, u) - y`
        -- TODO: this shouldn't be needed due to the next step
        stepFunction :: forall ctx' . Symbolic ctx' => Vector n (FieldElement ctx') -> Vector k (FieldElement ctx') -> Vector n (FieldElement ctx') -> Vector n (FieldElement ctx')
        stepFunction x u y = fromList $ toList (func x u) - toList y

        -- The circuit for one step of the recursion with full input
        -- TODO: apply the transformation that adds the output to the input and sets the new output to be `U1`
        stepCircuit' :: ArithmeticCircuit a (Vector n :*: Vector k :*: Vector n) (Vector n)
        stepCircuit' =
            hlmap (\(x :*: u :*: y) -> Comp1 (Par1 <$> x) :*: Comp1 (Par1 <$> u) :*: Comp1 (Par1 <$> y) :*: U1)
            $ hmap (\(Comp1 x') -> unPar1 <$> x')
            $ compile @a stepFunction

        -- The circuit for one step of the recursion with extra witness
        -- TODO: apply the transformation that removes a part of the input and sets it as an extra witness
        stepCircuit :: ArithmeticCircuit a (Vector n) (Vector n)
        stepCircuit = hlmap (\y -> tabulate (const (head y)) :*: tabulate (const (head y)) :*: y) stepCircuit'

        -- The Fiat-Shamired commit-open special-sound protocol for the circuit
        fs :: FiatShamir f (CommitOpen m c (ArithmeticCircuit a (Vector n) (Vector n)))
        fs = FiatShamir @f (CommitOpen @m @c stepCircuit)

        -- The verification function for the IVC instance-proof
        vf :: IVCInstanceProof pi f c m -> ((f, pi, f, c, c), (c, c))
        vf = ivcVerify' @pi @f @c @m fs

        -- TODO: the circuit input and output must be both transformed into `Vector n`
        circuit = compile @a vf
    in circuit
