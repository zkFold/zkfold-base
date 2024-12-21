{-# LANGUAGE AllowAmbiguousTypes #-}

module Tests.List (specList) where

import           Data.Binary                                 (Binary)
import qualified Data.Eq                                     as Haskell
import           Data.Function                               (($))
import           GHC.Generics                                (Par1 (..), U1 (..), type (:*:) (..))
import           System.IO                                   (IO)
import           Test.Hspec                                  (describe, hspec)
import           Test.Hspec.QuickCheck                       (prop)
import           Test.QuickCheck                             (Arbitrary)
import           Text.Show                                   (Show)

import           ZkFold.Base.Algebra.Basic.Class             (one)
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Class                       (Arithmetic, Symbolic)
import           ZkFold.Symbolic.Compiler                    (compile, eval1)
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.Eq                     ((==))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.Data.List                   (emptyList, head, tail, (.:))

headTest :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
headTest x y = head (x .: y .: emptyList) == x

tailTest :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
tailTest x y = head (tail (x .: y .: emptyList)) == y

specList' :: forall a. (Arbitrary a, Arithmetic a, Binary a, Show a) => IO ()
specList' = hspec $ describe "List spec" $ do
  prop "Head works fine" $ \x y ->
    eval1 (compile @a headTest) (U1 :*: U1 :*: U1) (Par1 x :*: Par1 y :*: U1)
      Haskell.== one
  prop "Tail works fine" $ \x y ->
    eval1 (compile @a tailTest) (U1 :*: U1 :*: U1) (Par1 x :*: Par1 y :*: U1)
      Haskell.== one

specList :: IO ()
specList = specList' @(Zp BLS12_381_Scalar)