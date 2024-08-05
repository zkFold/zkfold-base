{-# LANGUAGE AllowAmbiguousTypes #-}

module Tests.Protostar (specProtostar) where

import           Control.DeepSeq                                        (NFData)
import           Control.Monad                                          (replicateM)
import           Data.Map.Strict                                        (Map)
import qualified Data.Map.Strict                                        as M
import           GHC.Generics                                           (Generic)
import           Prelude                                                (IO, id, ($), (.), (<$>), (<*>), (<>), (==))
import qualified Prelude                                                as P
import qualified Test.Hspec
import           Test.Hspec                                             (Spec, describe, hspec)
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import qualified ZkFold.Base.Data.Vector                                as V
import           ZkFold.Base.Data.Vector                                (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound
import           ZkFold.Prelude                                         ((!!))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import qualified ZkFold.Symbolic.Data.Eq                                as Eq
import           ZkFold.Symbolic.Data.FieldElement                      (FieldElement)

data RecursiveFunction n a
    = RecursiveFunction
        { rIterations :: Natural
        , rInitial    :: Vector n a
        , rFunction   :: Vector n a -> Vector n a
        }

instance
    ( KnownNat n
    , Arbitrary a
    , AdditiveMonoid a
    , MultiplicativeSemigroup a
    ) => Arbitrary (RecursiveFunction n a) where
    -- Given a column-vector v, generate two random matrices L and R and compute (Lv *_h Rv) where *_h is Hadamard product
    -- This will construct a reasonably complicated recursive function for testing purposes
    arbitrary = do
        rIterations <- P.fromIntegral <$> chooseInteger (1, 10000)
        rInitial <- arbitrary
        vectorsL <- replicateM (P.fromIntegral $ value @n) arbitrary
        vectorsR <- replicateM (P.fromIntegral $ value @n) arbitrary
        let rFunction v = V.generate (\i -> sum ((*) <$> (vectorsL !! i) <*> v) * sum ((*) <$> (vectorsR !! i) <*> v))
        P.pure RecursiveFunction{..}

evaluateRF :: RecursiveFunction n a -> Vector n a
evaluateRF RecursiveFunction{..} = nTimes rIterations rFunction rInitial

-- I can't believe there is no such function in Prelude
nTimes :: Natural -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes 1 f = f
nTimes n f = f . nTimes (n -! 1) f

it :: Testable prop => P.String -> prop -> Spec
it desc prop = Test.Hspec.it desc (property prop)

specProtostarN
    :: forall a n
    .  Arbitrary a
    => Arithmetic a
    => KnownNat n
    => IO ()
specProtostarN = hspec $ do
    describe ("Test recursive functions of " <> P.show (value @n) <> " arguments") $
        it "folds correctly" $ \rf@RecursiveFunction{..} ->
            let FoldResult{..} = fold rFunction rIterations rInitial
             in verifierOutput === P.True .&&. deciderOutput === P.True .&&. output === evaluateRF (rf  :: RecursiveFunction n a)

specProtostar :: IO ()
specProtostar = do
    specProtostarN @(Zp BLS12_381_Scalar) @1
    specProtostarN @(Zp BLS12_381_Scalar) @2
    specProtostarN @(Zp BLS12_381_Scalar) @3
    specProtostarN @(Zp BLS12_381_Scalar) @10
    specProtostarN @(Zp BLS12_381_Scalar) @100
