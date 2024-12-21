{-# LANGUAGE AllowAmbiguousTypes #-}
module Tests.ReedSolomon where

import           GHC.Natural                                (Natural)
import           Prelude
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class hiding ((*), (+))
import qualified ZkFold.Base.Algebra.Basic.Class as C
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algorithm.ReedSolomon
import ZkFold.Base.Algebra.Polynomials.Univariate
import qualified Data.Vector as V
import qualified Prelude as P
import Data.Bool (bool)

data ReedSolomonExample f = ReedSolomonExample
    {
        char            :: Natural,  -- field order
        fElements       :: [f],     -- field elements
        primeElement    :: f,
        k               :: Int, -- message length
        t               :: Int, -- number of errors
        msg             :: [f],     -- message
        err           :: [f]      -- error polynomial
    } deriving (Show)

instance (Arbitrary f, FiniteField f, Eq f) => Arbitrary (ReedSolomonExample f) where
  arbitrary = do
    let c = order @f
    t <- chooseInt (1,5)
    let k = fromIntegral c P.- (2 * t)
        pe :: f = fromConstant (2 :: Natural)
        es = take (fromIntegral c) $ iterate (C.* pe) pe
    msg <- vector @f k
    er <- polyErr k t
    return $ ReedSolomonExample c es pe k t msg er


polyErr :: forall c. (Arbitrary c, Field c, Eq c) => Int -> Int -> Gen [c]
polyErr k t = do
    er <- genNErr @c t $ vector 0
    shuffle $ er ++ replicate (k P.- t) zero

genNErr :: forall c. (Arbitrary c, Field c, Eq c) => Int -> Gen [c] -> Gen [c]
genNErr 0 s = s
genNErr n s = do
    e <- arbitrary
    bool (genNErr (n P.-1) ((e :) <$> s)) (genNErr n s) (e == fromConstant (zero :: c))

----------------------------------------------------------------------------------------

propGenerator :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propGenerator ReedSolomonExample {..} =
    let vals = take (2*t) fElements
        polyGen = generator (k + 2 * t) k primeElement
    in all (\x -> evalPoly polyGen x == zero) vals && deg polyGen == fromIntegral (2*t)

propEncoder :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propEncoder ReedSolomonExample {..} =
    let encodedMsg = encode msg primeElement (k + 2 * t) k
        reminder = snd $ qr encodedMsg (generator (k + 2 * t) k primeElement)
        vals = take (2*t) fElements
    in all (\x -> evalPoly encodedMsg x == zero) vals && reminder == zero

propBerlekampNoError :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propBerlekampNoError ReedSolomonExample {..} =
    let
        vals = V.fromList $ take (2 P.* t) fElements
        encodedMsg = encode msg primeElement (k P.+ 2 P.* t) k
        syndromes = toPoly $ V.map (evalPoly encodedMsg) vals
    in syndromes == zero && berlekamp syndromes == (0, one)

propBerlekampWithErrors :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propBerlekampWithErrors ReedSolomonExample {..} =
    let
        vals = V.fromList $ take (2 P.* t) fElements
        encoded' = encode msg primeElement (k P.+ 2 P.* t) k
        errorMsg = toPoly $ V.fromList $ replicate (2*t) zero ++ err
        encoded = encoded' C.+ errorMsg
        syndromes = toPoly $ V.map (evalPoly encoded) vals
    in and $ zipWith (\s e -> evalPoly errorMsg e == s) (V.toList . fromPoly $ syndromes) (take (2 * t) fElements)

specReedSolomon :: IO ()
specReedSolomon = hspec $ do
    describe "Reed-Solomon" $ do
        it "generator function is correct" $ do
            property $ propGenerator @(Zp 17)
        it "encoder function is correct" $ do
            property $ propEncoder @(Zp 17)
        it "berlekamp function is correct with no errors" $ do
            property $ propBerlekampNoError @(Zp 17)
        it "berlekamp function is correct with errors" $ do
            property $ propBerlekampWithErrors @(Zp 17)
