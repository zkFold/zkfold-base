{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test2 (specArithmetization2) where

import           Data.Binary                                 (Binary)
import           GHC.Generics                                (Par1 (unPar1))
import           Prelude                                     hiding (Bool, Eq (..), Num (..), not, replicate, (/), (^),
                                                              (||))
import qualified Prelude                                     as Haskell
import           Test.Hspec
import           Test.QuickCheck                             (property)

import           ZkFold.Base.Algebra.Basic.Class             (one)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Base.Data.Vector                     (Vector, unsafeToVector)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.MonadCircuit                (Arithmetic)

-- A true statement.
tautology :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
tautology x y = (x /= y) || (x == y)

testTautology :: forall a . (Arithmetic a, Binary a) => a -> a -> Haskell.Bool
testTautology x y =
    let Bool (ac :: ArithmeticCircuit a (Vector 2) Par1) = compile @a (tautology @(ArithmeticCircuit a (Vector 2)))
        b       = unPar1 (eval ac (unsafeToVector [x, y]))
    in b Haskell.== one

specArithmetization2 :: Spec
specArithmetization2 = do
    describe "Arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> testTautology @Fr x y
