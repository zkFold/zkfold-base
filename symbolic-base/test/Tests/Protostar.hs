{-# LANGUAGE AllowAmbiguousTypes #-}

module Tests.Protostar (specProtostar) where

import           Prelude                           (IO)
import qualified Prelude                           as P

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector           (Vector)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)

data RecursiveFunction n c a
    = RecursiveFunction
        { rIterations :: Natural
        , rInitial    :: Vector n a
        , rFunction   :: Vector n (FieldElement c) -> Vector n (FieldElement c)
        }

instance P.Show a => P.Show (RecursiveFunction n c a) where
    show RecursiveFunction{..} = P.unlines [P.show rIterations, P.show rInitial]

-- instance
--     ( KnownNat n
--     , Arbitrary a
--     , Symbolic c
--     , MultiplicativeSemigroup (FieldElement c)
--     ) => Arbitrary (RecursiveFunction n c a) where
--     -- Given a column-vector v, generate two random matrices L and R and compute (Lv *_h Rv) where *_h is Hadamard product
--     -- This will construct a reasonably complicated recursive function for testing purposes
--     arbitrary = do
--         rIterations <- P.fromIntegral <$> chooseInteger (1, 100)
--         rInitial <- arbitrary
--         let generateFE  = fromConstant <$> chooseInteger (0, 10)
--             generateFEV = V.unsafeToVector <$> replicateM (P.fromIntegral $ value @n) generateFE
--         vectorsL <- replicateM (P.fromIntegral $ value @n) generateFEV
--         vectorsR <- replicateM (P.fromIntegral $ value @n) generateFEV
--         let rFunction v = V.generate (\i -> sum ((*) <$> (vectorsL !! i) <*> v) * sum ((*) <$> (vectorsR !! i) <*> v))
--         P.pure RecursiveFunction{..}

-- evaluateRF
--     :: forall n c a
--     .  c ~ ArithmeticCircuit a (Vector n)
--     => KnownNat n
--     => RecursiveFunction n c a
--     -> Vector n a
-- evaluateRF RecursiveFunction{..} =
--     let res = nTimes rIterations rFunction
--         ac  = compile @a res
--      in eval ac rInitial

-- -- I can't believe there is no such function in Prelude
-- nTimes :: Natural -> (a -> a) -> (a -> a)
-- nTimes 0 _ = id
-- nTimes 1 f = f
-- nTimes n f = f . nTimes (n -! 1) f

-- it :: Testable prop => P.String -> prop -> Spec
-- it desc prop = Test.Hspec.it desc (property prop)

-- specProtostarN
--     :: forall (c :: (Type -> Type) -> Type) n
--     .  KnownNat n
--     => c ~ ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector n)
--     => Symbolic c
--     => IO ()
-- specProtostarN = hspec $
--     describe ("Test recursive functions of " <> P.show (value @n) <> " arguments") $
--         it "folds correctly" $ withMaxSuccess 10 $ \(rf :: RecursiveFunction n c (Zp BLS12_381_Scalar)) -> P.undefined rf === (1 :: Natural)
{--
            let ProtostarResult{..} = iterate @c @n @(Point (Ed25519 c)) @(Zp BLS12_381_Scalar) rFunction rInitial rIterations
             in result === (fromConstant <$> evaluateRF (rf :: RecursiveFunction n c (Zp BLS12_381_Scalar)))
--}
-- TODO: fix the tests and their speed (requires at least in-circuit elliptic curves)

-- fib :: AdditiveSemigroup x => Vector 2 x -> Vector 2 x
-- fib x =
--     let [a, b] = toList x
--      in fromList [b, a + b]

specProtostar :: IO ()
specProtostar = do
    -- let ProtostarResult{..} = iterate fib (fromList [one :: Zp BLS12_381_Scalar, one]) 10
        -- RecursiveFunction{..} = RecursiveFunction 10 (fromList [one, one]) fib
    -- print result
    -- print $ evaluateRF (RecursiveFunction 10 (fromList [one, one]) fib)
    P.pure ()
{--  Too optimistic to think these tests will work fast enough...
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 1)) @1
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 2)) @2

    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 3)) @3
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 10)) @10
    specProtostarN @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 100)) @100
--}
