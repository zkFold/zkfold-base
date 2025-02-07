{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Symbolic.Algorithm.RSA (specRSA) where

import           Codec.Crypto.RSA                            (generateKeyPair)
import qualified Codec.Crypto.RSA                            as R
import           Data.Function                               (($))
import           GHC.Generics                                (Par1 (..))
import           Prelude                                     (pure)
import qualified Prelude                                     as P
import           System.Random                               (mkStdGen)
import           Test.Hspec                                  (Spec, describe)
import           Test.QuickCheck                             (Gen, withMaxSuccess, (.&.), (===))
import           Tests.Symbolic.ArithmeticCircuit            (it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Combinators            (ilog2)
import           ZkFold.Symbolic.Data.VarByteString          (fromNatural)
import           ZkFold.Symbolic.Interpreter                 (Interpreter (Interpreter))

type I = Interpreter Fr

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x -! 1)

evalBool :: forall a . Bool (Interpreter a) -> a
evalBool (Bool (Interpreter (Par1 v))) = v

specRSA :: Spec
specRSA = do
    describe "RSA signature" $ do
        it "encrypts and decrypts correctly" $ withMaxSuccess 10 $ do
            x <- toss $ (2 :: Natural) ^ (32 :: Natural)
            msgBits <- toss $ (2 :: Natural) ^ (256 :: Natural)
            let gen = mkStdGen (P.fromIntegral x)
                (R.PublicKey{..}, R.PrivateKey{..}, _) = generateKeyPair gen (P.fromIntegral $ value @KeyLength)
                prvkey = PrivateKey (fromConstant private_d) (fromConstant private_n)
                pubkey = PublicKey (fromConstant public_e) (fromConstant public_n)
                msg = fromConstant msgBits

                msgVar = fromNatural (ilog2 msgBits) msgBits

                sig = sign @I @256 msg prvkey
                check = verify @I @256 msg sig pubkey

                sigV = signVar @I @256 msgVar prvkey
                (checkV, _) = verifyVar @I @256 msgVar sigV pubkey

            pure $ evalBool check === one .&. evalBool checkV === one

