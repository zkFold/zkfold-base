{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Tests.Symbolic.Compiler (specCompiler) where

import           Data.Function                               (($))
import           Test.Hspec                                  (Spec, describe)
import           Tests.Symbolic.Compiler.CompileWith         (specCompileWith)
import           Tests.Symbolic.Compiler.Optimization        (specOptimization)
import           Tests.Symbolic.Compiler.Test1               (specArithmetization1)
import           Tests.Symbolic.Compiler.Test2               (specArithmetization2)
import           Tests.Symbolic.Compiler.Test3               (specArithmetization3)
import           Tests.Symbolic.Compiler.Test4               (specArithmetization4)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)

specCompiler :: Spec
specCompiler = do
  describe "Compiler specification" $ do
    specArithmetization1 @(Zp BLS12_381_Scalar)
    specArithmetization2
    specArithmetization3
    specArithmetization4
    specOptimization @(Zp BLS12_381_Scalar)
    specCompileWith @(Zp BLS12_381_Scalar)
