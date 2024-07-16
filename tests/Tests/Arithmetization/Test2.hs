{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Arithmetization.Test2 (specArithmetization2) where

import           Prelude                                     hiding (Bool, Eq (..), Num (..), not, replicate, (/), (^),
                                                              (||))
import qualified Prelude                                     as Haskell
import           Test.Hspec
import           Test.QuickCheck                             (property)

import           ZkFold.Base.Algebra.Basic.Class             (one)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Base.Data.Vector                     (item)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))

-- A true statement.
tautology :: (BoolType (Bool c), Eq (Bool c) (c 1)) => c 1 -> c 1 -> Bool c
tautology x y = (x /= y) || (x == y)

testTautology :: forall a . Arithmetic a => a -> a -> Haskell.Bool
testTautology x y =
    let Bool ac = compile @a (tautology @(ArithmeticCircuit a))
        b       = item $ acValue (applyArgs ac [x, y])
    in b Haskell.== one

specArithmetization2 :: Spec
specArithmetization2 = do
    describe "Arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> testTautology @Fr x y
