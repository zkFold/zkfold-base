{-# LANGUAGE AllowAmbiguousTypes #-}
module Tests.ReedSolomon where

import           Data.Bool                                  (bool)
import           Data.List                                  (sort)
import qualified Data.Vector                                as V
import           GHC.Natural                                (Natural)
import           Prelude
import qualified Prelude                                    as P
import           Test.Hspec
import           Test.QuickCheck

import qualified ZkFold.Base.Algebra.Basic.Class            as C
import           ZkFold.Base.Algebra.Basic.Class            hiding ((*), (+))
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Algorithm.ReedSolomon

data ReedSolomonExample f = ReedSolomonExample
    {
        char         :: Natural,  -- field order
        fElements    :: [f],     -- field elements
        primeElement :: f,
        k            :: Int,     -- message length
        r            :: Int,     -- number of errors * 2
        msg          :: [f],     -- message
        err          :: [f]      -- error polynomial
    } deriving (Show)

instance (Arbitrary f, FiniteField f, Eq f) => Arbitrary (ReedSolomonExample f) where
  arbitrary = do
    let c = order @f
    t <- chooseInt (1,P.div (fromIntegral c) 3)
    let r = 2*t
        k = fromIntegral c P.- r P.- 1
        pe = primElement @f
        es = take (fromIntegral c P.- 1) $ iterate (C.* pe) pe
    msg <- vector @f k
    er <- polyErr (k+t) t
    return $ ReedSolomonExample c es pe k r msg er

primElement :: forall f. FiniteField f => f
primElement = case order @f of
    7  -> fromConstant (3 :: Natural)
    17 -> fromConstant (3 :: Natural)
    _  -> error "can't find primitive element of field"


polyErr :: forall c. (Arbitrary c, Field c) => Int -> Int -> Gen [c]
polyErr kt t = do
    pos <- shuffle (replicate t (1 :: Integer) P.++ replicate kt 0)
    mapM (\p -> bool arbitrary (pure zero) (p==0) ) pos

----------------------------------------------------------------------------------------

propGenerator :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propGenerator ReedSolomonExample {..} =
    let vals = take r fElements
        polyGen = generator r primeElement
    in all (\x -> evalPoly polyGen x == zero) vals

propEncoder :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propEncoder ReedSolomonExample {..} =
    let encodedMsg = encode msg primeElement r
        reminder = snd $ qr encodedMsg (generator r primeElement)
    in deg reminder == -1

propBerlekampNoError :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propBerlekampNoError ReedSolomonExample {..} =
    let
        vals = V.fromList $ take r fElements
        encodedMsg = encode msg primeElement r
        syndromes = toPoly $ V.map (evalPoly encodedMsg) vals
    in syndromes == zero && berlekamp syndromes r == (0, one)

propBerlekampWithErrors :: forall c. (Field c, Ord c) => ReedSolomonExample c -> Bool
propBerlekampWithErrors ReedSolomonExample {..} =
    let
        vals = V.fromList $ take r fElements
        encoded' = encode msg primeElement r
        errorMsg = toPoly $ V.fromList err
        encoded = encoded' C.+ errorMsg
        syndromes = toPoly $ V.map (evalPoly encoded) vals
        bl = snd $ berlekamp syndromes r
        roots = filter (/= zero) $ map (\x -> bool zero x (evalPoly bl x == zero)) fElements

        es1 = take (fromIntegral char P.- 1) $ iterate (C.* primeElement) one
        rightLocators = filter (/= zero) $ zipWith (\e pe -> bool zero (finv pe) (e /= zero)) err es1
    in sort roots == sort rightLocators

propDecodeWithoutError :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propDecodeWithoutError ReedSolomonExample {..} =
    let encoded = encode msg primeElement r
        decoded = decode encoded primeElement (fromIntegral char P.- 1) r
    in toPoly (V.fromList msg) == decoded

propDecodeWithError :: forall c. (Field c, Eq c) => ReedSolomonExample c -> Bool
propDecodeWithError ReedSolomonExample {..} =
    let encoded' = encode msg primeElement r
        errorMsg = toPoly $ V.fromList err
        encoded = encoded' C.+ errorMsg
        decoded = decode encoded primeElement (fromIntegral char P.- 1) r
    in toPoly (V.fromList msg) == decoded

specReedSolomon :: IO ()
specReedSolomon = hspec $ do
    describe "Reed-Solomon" $ do
        it "generator function is correct" $ do
            property $ propGenerator @(Zp 17)
        it "encoder function is correct" $ do
            property $ propEncoder @(Zp 17)
        it "berlekamp function is correct without errors" $ do
            property $ propBerlekampNoError @(Zp 17)
        it "berlekamp function is correct with errors" $ do
            property $ propBerlekampWithErrors @(Zp 17)
        it "decode function is correct without errors" $ do
            property $ propDecodeWithoutError @(Zp 17)
        it "decode function is correct with errors" $ do
            property $ propDecodeWithError @(Zp 17)
