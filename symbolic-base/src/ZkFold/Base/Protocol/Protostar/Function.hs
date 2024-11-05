{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Base.Protocol.Protostar.Function where


import           Data.Map.Strict                                     (elems)
import qualified Data.Map.Strict                                     as M
import           Prelude                                             (type (~), ($))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                             (Vector, drop, take, append)
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound         as SPS
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import ZkFold.Symbolic.Data.Input (SymbolicInput)
import ZkFold.Symbolic.Data.Class (SymbolicData(..))
import GHC.Generics (U1(..), (:*:)(..))
import ZkFold.Base.Data.ByteString (Binary)
import ZkFold.Base.Protocol.Protostar.ArithmeticCircuit ()

instance (KnownNat n, KnownNat m, m ~ n + n, Arithmetic a, Binary a, AdditiveGroup pi, SymbolicInput pi, Context pi ~ ArithmeticCircuit a (Layout pi :*: Layout pi :*: U1), Layout pi ~ Vector n)
            => SPS.SpecialSoundProtocol a (pi -> pi) where
        type Witness a (pi -> pi) = ()
        type Input a (pi -> pi) = (Layout pi :*: Layout pi) a
        type ProverMessage a (pi -> pi) = [a]
        type VerifierMessage a (pi -> pi) = a
        type VerifierOutput a (pi -> pi)  = [a]
        type Degree (pi -> pi) = 2

        -- One round for Plonk
        rounds = P.const 1

        outputLength func =
            let func' x y = func x - y
                ac = hlmap (\xy -> take @n xy :*: (drop @n xy :*: U1)) $ compile @a func'
            in P.fromIntegral $ M.size (acSystem ac)

        -- The transcript will be empty at this point, it is a one-round protocol.
        -- Input is arithmetised. We need to combine its witness with the circuit's witness.
        --
        prover func _ (i :*: o) _ _ =
            let func' x y = func x - y
                ac = hlmap (\xy -> take @n xy :*: (drop @n xy :*: U1)) $ compile @a func'
                pi = i `append` o
            in elems $ witnessGenerator ac pi

        -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
        --
        verifier func (i :*: o) pm ts =
            let func' x y = func x - y
                ac = hlmap (\xy -> take @n xy :*: (drop @n xy :*: U1)) $ compile @a func'
                pi = i `append` o
            in SPS.algebraicMap ac pi pm ts one
