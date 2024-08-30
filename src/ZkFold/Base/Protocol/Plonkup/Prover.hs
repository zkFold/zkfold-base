{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover
    ( module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
    , module ZkFold.Base.Protocol.Plonkup.Prover.Secret
    , module ZkFold.Base.Protocol.Plonkup.Prover.Setup
    ) where

import qualified Data.Vector                                         as V
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkPolyExtended)
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..))

import          ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
import          ZkFold.Base.Protocol.Plonkup.Prover.Secret
import          ZkFold.Base.Protocol.Plonkup.Prover.Setup