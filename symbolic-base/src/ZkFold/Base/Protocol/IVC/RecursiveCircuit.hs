{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.RecursiveCircuit where

import           GHC.Generics                                    (Par1 (..), U1 (..), type (:.:) (..), (:*:) (..))
import           Prelude                                         hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                (KnownNat, type (+), type (-), value)
import           ZkFold.Base.Data.ByteString                     (Binary)
import           ZkFold.Base.Data.Vector                         (Vector, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.ArithmetizableFunction (ArithmetizableFunction (ArithmetizableFunction))
import           ZkFold.Base.Protocol.IVC.Commit                 (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen             (CommitOpen (..))
import           ZkFold.Base.Protocol.IVC.FiatShamir             (FiatShamir (..))
import           ZkFold.Base.Protocol.IVC.Internal               (IVCResult, ivcVerify)
import           ZkFold.Prelude                                  (replicate)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Class                      (SymbolicData (..))
import           ZkFold.Symbolic.Data.FieldElement               (FieldElement (..))
import           ZkFold.Symbolic.Data.Input                      (SymbolicInput)
import           ZkFold.Symbolic.Interpreter                     (Interpreter (..))

-- | Takes a function `f` and returns a circuit `C` with input `y` and witness `w`.
-- The circuit is such that `C(y, w) = 0` implies that `y = x(n)` for some positive `n` where
-- `x(k+1) = f(x(k), u(k))` for all `k` and some `u`.
protostar :: forall f i m c d k a payload input output nx nu ctx .
    ( f ~ FieldElement ctx
    , i ~ Vector nx
    , m ~ [f]
    , c ~ f
    , HomomorphicCommit m c
    , KnownNat (d - 1)
    , KnownNat (d + 1)
    , KnownNat k
    , KnownNat (k - 1)
    , Binary a
    , Arithmetic a
    , KnownNat nx
    , KnownNat nu
    , ctx ~ ArithmeticCircuit a payload input
    , SymbolicInput (IVCResult f i m c d k)
    , Context (IVCResult f i m c d k) ~ ctx
    , payload ~ (Payload (IVCResult f i m c d k) :*: U1)
    , input ~ (Layout (IVCResult f i m c d k) :*: U1)
    , output ~ (((Par1 :*: (Vector nx :.: Par1)) :*: ((Vector (k - 1) :.: Par1) :*: ((Vector k :.: Par1) :*: Par1))) :*: ((Vector k :.: Par1) :*: Par1))
    ) => (forall ctx' . Symbolic ctx' => Vector nx (FieldElement ctx') -> Vector nu (FieldElement ctx') -> Vector nx (FieldElement ctx'))
    -> ArithmeticCircuit a payload input output
protostar func =
    let
        -- The numeric interpretation of the function `f`.
        stepFunction :: Vector nx a -> Vector nu a -> Vector nx a
        stepFunction x' u' =
            let x = fromConstant <$> x' :: Vector nx (FieldElement (Interpreter a))
                u = fromConstant <$> u' :: Vector nu (FieldElement (Interpreter a))
            in unPar1 . runInterpreter . fromFieldElement <$> func x u

        -- The step circuit for the recursion implements the function `F(x, u, y) = f(x, u) - y`.
        -- Here `x` and `u` are the private inputs and `y` is the public input.
        stepCircuit :: ArithmeticCircuit a (Vector nx :*: Vector nu) (Vector nx) U1
        stepCircuit =
            hpmap (\(x :*: u) -> Comp1 (Par1 <$> x) :*: Comp1 (Par1 <$> u)) $
            hlmap (\x -> U1 :*: Comp1 (Par1 <$> x)) $
            compileWith @a guessOutput (\(x :*: u) U1 ->
                    ( Comp1 (unsafeToVector $ replicate (value @nx) U1) :*: Comp1 (unsafeToVector $ replicate (value @nx) U1) :*: U1
                    , x :*: u :*: U1)
                ) func

        -- Protostar IVC takes an arithmetizable function as input.
        af :: ArithmetizableFunction a (Vector nx) (Vector nu)
        af = ArithmetizableFunction stepFunction stepCircuit

        -- The Fiat-Shamired commit-open special-sound protocol for the arithmetizable function
        fs :: FiatShamir (CommitOpen (ArithmetizableFunction a (Vector nx) (Vector nu)))
        fs = FiatShamir (CommitOpen af)

        -- The verification function for the IVC result object
        vf :: IVCResult f i m c d k -> ((f, i f, Vector (k-1) f, Vector k c, c), (Vector k c, c))
        vf = ivcVerify @f @i @m @c @d @k fs

        -- -- TODO: the circuit functors must be adjusted for better usability
        circuit = compile @a vf
    in circuit
