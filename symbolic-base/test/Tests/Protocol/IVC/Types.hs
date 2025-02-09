{-# LANGUAGE TypeOperators       #-}

module Tests.Protocol.IVC.Types where

import           GHC.Generics                               (U1 (..), type (:*:) (..))
import           Prelude                                    hiding (Bool (..), Num (..), pi, replicate, sum, (+))

import qualified ZkFold.Base.Algebra.EllipticCurve.Pasta    as Pasta
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec)
import           ZkFold.Base.Data.Vector                    (Vector (..))
import           ZkFold.Base.Protocol.IVC.Commit            ()
import           ZkFold.Base.Protocol.IVC.FiatShamir        (FiatShamir)
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..))
import           ZkFold.Symbolic.Compiler                   (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (..))
import           ZkFold.Symbolic.Data.FieldElementW         (FieldElementW, constrainFieldElement)
import           ZkFold.Symbolic.Data.Pasta                 (PallasPoint)
import           ZkFold.Symbolic.Interpreter                (Interpreter)

type A = Pasta.Fp
type C = PallasPoint
type I = Vector 1
type P = U1
type K = 1
type CTX = Interpreter A
type AC = ArithmeticCircuit A (Vector 1 :*: U1) (Vector 1) (Vector 1)
type W = FieldElementW CTX
type F = FieldElement CTX
type PHI = Predicate A I P
type SPS = FiatShamir 1 A I P C
type D = 2
type PARDEG = 5
type PAR = PolyVec A PARDEG

fromWitness :: Traversable t => t W -> t F
fromWitness = fmap constrainFieldElement
