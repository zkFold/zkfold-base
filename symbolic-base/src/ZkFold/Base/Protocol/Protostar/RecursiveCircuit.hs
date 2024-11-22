{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.Protostar.RecursiveCircuit where

-- import           Data.Functor.Rep                          (tabulate)
-- import           GHC.Generics                              (Par1 (..), U1 (..), type (:.:) (..), (:*:) (..))
-- import           GHC.IsList                                (IsList (..))
-- import           Prelude                                   hiding (Num (..), drop, head, take, zipWith)

-- import           ZkFold.Base.Algebra.Basic.Class
-- import           ZkFold.Base.Algebra.Basic.Number          (KnownNat, type (+), type (-))
-- import           ZkFold.Base.Data.ByteString               (Binary)
-- import           ZkFold.Base.Data.HFunctor                 (hmap)
-- import           ZkFold.Base.Data.Vector                   (Vector, head)
-- import           ZkFold.Base.Protocol.Protostar.Commit     (HomomorphicCommit)
-- import           ZkFold.Base.Protocol.Protostar.CommitOpen (CommitOpen (..))
-- import           ZkFold.Base.Protocol.Protostar.FiatShamir (FiatShamir (..))
-- import           ZkFold.Base.Protocol.Protostar.IVC        (IVCInstanceProof, ivcVerify)
-- import           ZkFold.Symbolic.Class
-- import           ZkFold.Symbolic.Compiler
-- import           ZkFold.Symbolic.Data.Class                (SymbolicData (..))
-- import           ZkFold.Symbolic.Data.FieldElement         (FieldElement (..))
-- import           ZkFold.Symbolic.Data.Input                (SymbolicInput)

-- -- | Takes a function `f` and returns a circuit `C` with input `y` and witness `w`.
-- -- The circuit is such that `C(y, w) = 0` implies that `y = x(n)` for some positive `n` where
-- -- `x(k+1) = f(x(k), u(k))` for all `k` and some `u`.
-- protostar :: forall f i m c d k a input output nx nu ctx .
--     ( f ~ FieldElement ctx
--     , i ~ Vector nx
--     , m ~ [f]
--     , c ~ f
--     , HomomorphicCommit m c
--     , KnownNat (d - 1)
--     , KnownNat (d + 1)
--     , KnownNat k
--     , KnownNat (k - 1)
--     , Binary a
--     , Arithmetic a
--     , input ~ Layout (IVCInstanceProof f i m c d k) :*: U1
--     , output ~ (((Par1 :*: (Vector nx :.: Par1)) :*: ((Vector (k - 1) :.: Par1) :*: ((Vector k :.: Par1) :*: Par1))) :*: ((Vector k :.: Par1) :*: Par1))
--     , KnownNat nx
--     , KnownNat nu
--     , ctx ~ ArithmeticCircuit a input
--     , SymbolicInput (IVCInstanceProof f i m c d k)
--     , Context (IVCInstanceProof f i m c d k) ~ ctx
--     ) => (forall ctx' . Symbolic ctx' => Vector nx (FieldElement ctx') -> Vector nu (FieldElement ctx') -> Vector nx (FieldElement ctx'))
--     -> ArithmeticCircuit a input output
-- protostar func =
--     let
--         -- The step function for the recursion: `F(x, u, y) = f(x, u) - y`
--         -- TODO: this shouldn't be needed due to the next step
--         stepFunction :: forall ctx' . Symbolic ctx' => Vector nx (FieldElement ctx') -> Vector nu (FieldElement ctx') -> Vector nx (FieldElement ctx') -> Vector nx (FieldElement ctx')
--         stepFunction x u y = fromList $ toList (func x u) - toList y

--         -- The circuit for one step of the recursion with full input
--         -- TODO: apply the transformation that adds the output to the input and sets the new output to be `U1`
--         stepCircuit' :: ArithmeticCircuit a (Vector nx :*: Vector nu :*: Vector nx) (Vector nx)
--         stepCircuit' =
--             hlmap (\(x :*: u :*: y) -> Comp1 (Par1 <$> x) :*: Comp1 (Par1 <$> u) :*: Comp1 (Par1 <$> y) :*: U1)
--             $ hmap (\(Comp1 x') -> unPar1 <$> x')
--             $ compile @a stepFunction

--         -- The circuit for one step of the recursion with extra witness
--         -- TODO: apply the transformation that removes a part of the input and sets it as an extra witness
--         stepCircuit :: ArithmeticCircuit a (Vector nx) (Vector nx)
--         stepCircuit = hlmap (\y -> tabulate (const (head y)) :*: tabulate (const (head y)) :*: y) stepCircuit'

--         -- The Fiat-Shamired commit-open special-sound protocol for the circuit
--         fs :: FiatShamir (CommitOpen (ArithmeticCircuit a (Vector nx) (Vector nx)))
--         fs = FiatShamir (CommitOpen stepCircuit)

--         -- The verification function for the IVC instance-proof
--         vf :: IVCInstanceProof f i m c d k -> ((f, i f, Vector (k-1) f, Vector k c, c), (Vector k c, c))
--         vf = ivcVerify @f @i @m @c @d @k fs

--         -- TODO: the circuit input and output must be both transformed into `Vector n`
--         circuit = compile @a vf
--     in circuit
