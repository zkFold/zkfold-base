{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Protostar (specProtostar) where

import           Control.Monad                               (replicateM)
import           Data.Kind                                   (Type)
import qualified Data.Map.Strict                             as M
import           Prelude                                     (IO, id, type (~), ($), (.), (<$>), (<*>), (<>))
import qualified Prelude                                     as P
import qualified Test.Hspec
import           Test.Hspec                                  (Spec, describe, hspec)
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar
import           ZkFold.Prelude                              ((!!))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

data RecursiveFunction n c a
    = RecursiveFunction
        { rIterations :: Natural
        , rInitial    :: Vector n a
        , rFunction   :: Vector n (FieldElement c) -> Vector n (FieldElement c)
        }

instance P.Show (RecursiveFunction n c a) where
    show _ = "Dummy Show instance required by HSpec"

instance
    ( KnownNat n
    , Arbitrary a
    , Symbolic c
    , Bits (BaseField c) ~ [BaseField c]
    ) => Arbitrary (RecursiveFunction n c a) where
    -- Given a column-vector v, generate two random matrices L and R and compute (Lv *_h Rv) where *_h is Hadamard product
    -- This will construct a reasonably complicated recursive function for testing purposes
    arbitrary = do
        rIterations <- P.fromIntegral <$> chooseInteger (1, 100)
        rInitial <- arbitrary
        let generateFE  = fromConstant <$> chooseInteger (0, 10)
            generateFEV = V.unsafeToVector <$> replicateM (P.fromIntegral $ value @n) generateFE
        vectorsL <- replicateM (P.fromIntegral $ value @n) generateFEV
        vectorsR <- replicateM (P.fromIntegral $ value @n) generateFEV
        let rFunction v = V.generate (\i -> sum ((*) <$> (vectorsL !! i) <*> v) * sum ((*) <$> (vectorsR !! i) <*> v))
        P.pure RecursiveFunction{..}

evaluateRF
    :: forall n c a
    .  TypeSize (ArithmeticCircuit a) (FieldElement c) ~ 1
    => Support (ArithmeticCircuit a) (FieldElement c) ~ ()
    => SymbolicData (ArithmeticCircuit a) (FieldElement c)
    => P.Eq a
    => MultiplicativeMonoid a
    => KnownNat n
    => RecursiveFunction n c a
    -> Vector n a
evaluateRF RecursiveFunction{..} =
    let res = nTimes rIterations rFunction
        ac  = compile @a res
     in eval ac (M.fromList $ P.zip [1..] (V.fromVector rInitial))
-- I can't believe there is no such function in Prelude
nTimes :: Natural -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes 1 f = f
nTimes n f = f . nTimes (n -! 1) f

it :: Testable prop => P.String -> prop -> Spec
it desc prop = Test.Hspec.it desc (property prop)

specProtostarN
    :: forall (c :: (Type -> Type) -> Type) n
    .  KnownNat n
    => TypeSize (ArithmeticCircuit (Zp BLS12_381_Scalar)) (FieldElement c) ~ 1
    => Support (ArithmeticCircuit (Zp BLS12_381_Scalar)) (FieldElement c) ~ ()
    => SymbolicData (ArithmeticCircuit (Zp BLS12_381_Scalar)) (FieldElement c)
    => Symbolic c
    => IO ()
specProtostarN = hspec $ do
    describe ("Test recursive functions of " <> P.show (value @n) <> " arguments") $
        it "folds correctly" $ \rf@RecursiveFunction{..} ->
            let FoldResult{..} = fold rFunction rIterations rInitial
             in verifierOutput === P.True .&&. deciderOutput === P.True .&&. output === evaluateRF (rf :: RecursiveFunction n c (Zp BLS12_381_Scalar))

specProtostar :: IO ()
specProtostar = do
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @1
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @2
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @3
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @10
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @100
