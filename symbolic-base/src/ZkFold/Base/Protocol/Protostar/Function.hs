{-# LANGUAGE TypeOperators           #-}

module ZkFold.Base.Protocol.Protostar.Function where


import           Data.Zip                                         (zipWith)
import           GHC.Generics                                     (Par1 (..), U1 (..), (:*:) (..), (:.:) (..))
import           GHC.IsList                                       (toList)
import           Prelude                                          (foldl, fst, type (~), ($), (.))
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Univariate       (PolyVec)
import           ZkFold.Base.Data.ByteString                      (Binary)
import           ZkFold.Base.Data.Vector                          (Vector, append, drop, take)
import           ZkFold.Base.Protocol.Protostar.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen        (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir        (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.IVC               (IVCInstanceProof (..), ivcInitialize, ivcIterate)
import           ZkFold.Base.Protocol.Protostar.Oracle            (RandomOracle)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.FieldElement                (FieldElement (..))
import           ZkFold.Symbolic.Interpreter                      (Interpreter (..))

functionfToCircuit :: forall a n m i o.
    ( KnownNat n
    , KnownNat m
    , m ~ n + n
    , Arithmetic a
    , Binary a
    , i ~ Vector m
    , o ~ (Vector n :.: Par1)
    ) => (forall c. Symbolic c => Vector n (FieldElement c) -> Vector n (FieldElement c)) -> ArithmeticCircuit a i o
functionfToCircuit func =
    let func' x = zipWith (-) (func x)
    in
        hlmap (\xy -> Comp1 (Par1 P.<$> take @n xy) :*: (Comp1 (Par1 P.<$> drop @n xy) :*: U1)) $
         compile @a func'

-- | Takes a function f and an input x and returns an instance-proof pair for (f^(n-1)(x), f^n(x)). Number n must be positive.
proveFunctionImage :: forall pi f c m n k .
    ( KnownNat n
    , KnownNat k
    , k ~ n + n
    , Arithmetic f
    , Ring (PolyVec f 3) -- I don't know why this one is not inferred
    , Binary f
    , pi ~ [f]
    , Scale f c
    , RandomOracle f f
    , RandomOracle pi f
    , RandomOracle c f
    , HomomorphicCommit m c
    , m ~ [f]
    )
    => (forall ctx . Symbolic ctx => Vector n (FieldElement ctx) -> Vector n (FieldElement ctx))
    -> Vector n f
    -> Natural
    -> IVCInstanceProof pi f c m
proveFunctionImage func x0 n =
    let ac = functionfToCircuit @f func :: ArithmeticCircuit f (Vector k) (Vector n :.: Par1)
        fs = FiatShamir (CommitOpen ac)

        step :: (IVCInstanceProof pi f c m, Vector n f) -> Natural -> (IVCInstanceProof pi f c m, Vector n f)
        step (ip, x) _ =
            let x' = FieldElement . Interpreter . Par1 P.<$> x
                y = unPar1 . runInterpreter . fromFieldElement P.<$> func x'
            in (ivcIterate @f fs ip (toList $ x `append` y), y)

    in fst $ foldl step (ivcInitialize, x0) [1..n]

-- proveRecursion ::
--     (pi -> pi) -> pi -> Natural -> IVCInstanceProof pi f c m
-- proveRecursion func pi n =
--     let
--         ac = recursiveFunctionfToCircuit @a @n func
--         pi' = pi `append` pi
--     in IVCInstanceProof pi' (elems $ witnessGenerator ac pi') n

-- instance (KnownNat n, KnownNat m, m ~ n + n, Arithmetic a, Binary a, AdditiveGroup pi, SymbolicInput pi, Context pi ~ ArithmeticCircuit a (Layout pi :*: Layout pi :*: U1), Layout pi ~ Vector n)
--             => SPS.SpecialSoundProtocol a (pi -> pi) where
--         type Witness a (pi -> pi) = ()
--         type Input a (pi -> pi) = (Layout pi :*: Layout pi) a
--         type ProverMessage a (pi -> pi) = [a]
--         type VerifierMessage a (pi -> pi) = a
--         type VerifierOutput a (pi -> pi)  = [a]
--         type Degree (pi -> pi) = 2

--         -- One round for Plonk
--         rounds = P.const 1

--         outputLength func =
--             let func' x y = func x - y
--                 ac = hlmap (\xy -> take @n xy :*: (drop @n xy :*: U1)) $ compile @a func'
--             in P.fromIntegral $ M.size (acSystem ac)

--         -- The transcript will be empty at this point, it is a one-round protocol.
--         -- Input is arithmetised. We need to combine its witness with the circuit's witness.
--         --
--         prover func _ (i :*: o) _ _ =
--             let func' x y = func x - y
--                 ac = hlmap (\xy -> take @n xy :*: (drop @n xy :*: U1)) $ compile @a func'
--                 pi = i `append` o
--             in elems $ witnessGenerator ac pi

--         -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
--         --
--         verifier func (i :*: o) pm ts =
--             let func' x y = func x - y
--                 ac = hlmap (\xy -> take @n xy :*: (drop @n xy :*: U1)) $ compile @a func'
--                 pi = i `append` o
--             in SPS.algebraicMap ac pi pm ts one
