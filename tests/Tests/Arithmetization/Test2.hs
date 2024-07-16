{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Arithmetization.Test2 (specArithmetization2) where

import           Prelude                                     hiding (Bool, Eq (..), Num (..), not, replicate, (/), (^),
                                                              (||))
import qualified Prelude                                     as Haskell
import           Test.Hspec
import           Test.QuickCheck                             (property)

import           ZkFold.Base.Algebra.Basic.Class             (BinaryExpansion, Bits)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Types                       (Symbolic)

-- A true statement.
tautology :: forall c a . Eq (Bool (c 1 a)) (c 1 a) => c 1 a -> c 1 a -> Bool (c 1 a)
tautology x y = (x /= y) || (x == y)

testTautology :: forall a . (Symbolic a, BinaryExpansion a, Haskell.Eq a, Bits a ~ [a])
    => a -> a -> Haskell.Bool
testTautology x y =
    let Bool ac = compile @a (tautology @ArithmeticCircuit @a)
        b       = Bool $ acValue (applyArgs ac [x, y])
    in b Haskell.== true

specArithmetization2 :: Spec
specArithmetization2 = do
    describe "Arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> testTautology @Fr x y
