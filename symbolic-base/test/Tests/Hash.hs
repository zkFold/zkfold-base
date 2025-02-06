{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Tests.Hash (specHash) where

import           Data.Binary                                 (Binary)
import qualified Data.Eq                                     as Haskell
import           Data.Function                               (($))
import           GHC.Generics                                (Par1 (Par1), U1 (..), type (:*:) (..))
import           System.IO                                   (IO)
import           Test.Hspec                                  (describe, hspec)
import           Test.Hspec.QuickCheck                       (prop)
import           Test.QuickCheck                             (Arbitrary)
import           Text.Show                                   (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Class                       (Arithmetic, Symbolic)
import           ZkFold.Symbolic.Compiler                    (compile, eval1)
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.Eq                     ((==))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.Data.Hash                   (Hashable (..), hash, preimage)
import Data.Typeable (Typeable)

instance Symbolic c => Hashable (FieldElement c) (FieldElement c) where
  hasher _ = zero

hashTest :: forall c. Symbolic c => FieldElement c -> Bool c
hashTest e = preimage @(FieldElement c) (hash e) == e

specHash' :: forall a. (Arbitrary a, Arithmetic a, Binary a, Show a, Typeable a) => IO ()
specHash' = hspec $ describe "Hash spec" $ prop "Preimage works fine" $ \x ->
    eval1 (compile @a hashTest) (U1 :*: U1) (Par1 x :*: U1) Haskell.== one

specHash :: IO ()
specHash = specHash' @(Zp BLS12_381_Scalar)
