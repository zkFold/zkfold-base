{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

{-# OPTIONS_GHC -Wno-orphans #-}

import           Control.Applicative                         ((<*>))
import           Control.Monad                               (return)
import           Data.Eq                                     (Eq)
import           Data.Function                               (const, ($))
import           Data.Functor                                (Functor, (<$>))
import           GHC.Generics                                (Par1 (..), U1 (..), (:*:) (..))
import           System.IO                                   (IO)
import           Test.QuickCheck
import           Test.Tasty                                  (defaultMain)
import           Test.Tasty.QuickCheck                       (testProperties)
import           Text.Show                                   (Show)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Base)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compile)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit  (eval)
import           ZkFold.Symbolic.Data.Bool                   (false, true)
import           ZkFold.Symbolic.Data.Class                  (SymbolicData (..))
import           ZkFold.Symbolic.Data.Input                  (SymbolicInput)
import           ZkFold.Symbolic.UPLC.Converter              (contractV3)
import           ZkFold.UPLC.BuiltinFunction
import           ZkFold.UPLC.Term

areSame ::
  ( SymbolicData f, Context f ~ c, Support f ~ s, Layout f ~ l
  , c ~ ArithmeticCircuit a i, Arbitrary (i a), Show (i a)
  , SymbolicInput s, Context s ~ c, Layout s ~ i
  , Functor l, Eq (l a), Show (l a)
  , a ~ Zp BLS12_381_Base) =>
  (Term -> f) -> Term -> f -> Property
areSame v t f =
  let acT = compile (v t)
      acF = compile f
   in property $ \i -> eval acT i === eval acF i

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary ((f :*: g) a) where
  arbitrary = (:*:) <$> arbitrary <*> arbitrary

instance Arbitrary (U1 a) where
  arbitrary = return U1

instance Arbitrary a => Arbitrary (Par1 a) where
  arbitrary = Par1 <$> arbitrary

tFalse, tTrue, tUnit :: Term
tFalse = TConstant (CBool false)
tTrue = TConstant (CBool true)
tUnit = TConstant (CUnit ())

infixl 1 $$
($$) :: Term -> Term -> Term
($$) = TApp

prop_triv :: Property
prop_triv = areSame contractV3 (TLam tFalse) (const true)

prop_err :: Property
prop_err = areSame contractV3 (TLam TError) (const false)

prop_sub :: Property
prop_sub =
  areSame contractV3 (TLam $ TLam (TVariable 0) $$ tTrue) (const true)

prop_pair_ok :: Property
prop_pair_ok = areSame contractV3
  (TLam $ TBuiltin (BFPoly FstPair) $$ TConstant (CPair (CUnit ()) (CBool false)))
  (const true)

prop_pair_err :: Property
prop_pair_err =
  areSame contractV3 (TLam $ TBuiltin (BFPoly SndPair) $$ tTrue) (const false)

prop_if_triv :: Property
prop_if_triv = areSame contractV3
  (TLam $ TBuiltin (BFPoly IfThenElse) $$ tTrue $$ tTrue $$ tFalse)
  (const true)

prop_if_ok :: Property
prop_if_ok = areSame contractV3
  (TLam $ TBuiltin (BFPoly IfThenElse) $$ tTrue $$ tUnit $$ TError)
  (const true)

prop_if_err :: Property
prop_if_err = areSame contractV3
  (TLam $ TBuiltin (BFPoly IfThenElse) $$ tFalse $$ tUnit $$ TError)
  (const false)

prop_if_sub :: Property
prop_if_sub = areSame contractV3
  (TLam $ TLam (TVariable 0 $$ tTrue $$ tUnit $$ TError) $$ TBuiltin (BFPoly IfThenElse))
  (const true)

return []
main :: IO ()
main = defaultMain $ testProperties "UPLC tests" $allProperties
