{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Tests.Compiler (specCompiler) where

import           Control.Applicative                         ((<*>))
import           Control.Monad                               (return)
import           Data.Binary                                 (Binary)
import           Data.Function                               (($))
import           Data.Functor                                ((<$>))
import           GHC.Generics                                (U1 (..), (:*:) (..))
import           System.IO                                   (IO)
import           Test.Hspec                                  (describe, hspec)
import           Test.Hspec.QuickCheck                       (prop)
import           Test.QuickCheck                             (Arbitrary (..))
import           Text.Show                                   (Show)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Class                       (Arithmetic, Symbolic)
import           ZkFold.Symbolic.Compiler                    (finalRestore, guessOutput, isConstantInput,
                                                              payloadCircuit, solderWith)
import           ZkFold.Symbolic.Data.Bool                   ((&&))
import           ZkFold.Symbolic.Data.ByteString             (ByteString)

testFunction :: Symbolic c => ByteString 256 c -> ByteString 256 c -> ByteString 256 c
testFunction = (&&)

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary ((f :*: g) a) where
  arbitrary = (:*:) <$> arbitrary <*> arbitrary

instance Arbitrary (U1 a) where
  arbitrary = return U1

specCompilerG :: forall a. (Arbitrary a, Arithmetic a, Binary a, Show a) => IO ()
specCompilerG = hspec $ describe "Compiler specification" $ do
  prop "Guessing with payload is constant in input" $ isConstantInput $
    finalRestore $ guessOutput @a @_ @U1 $ solderWith payloadCircuit testFunction

specCompiler :: IO ()
specCompiler = specCompilerG @(Zp BLS12_381_Scalar)
