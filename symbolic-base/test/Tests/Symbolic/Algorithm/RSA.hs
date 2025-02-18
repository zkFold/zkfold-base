{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Symbolic.Algorithm.RSA (specRSA) where

import           Codec.Crypto.RSA                            (generateKeyPair)
import qualified Codec.Crypto.RSA                            as R
import           System.Random                               (RandomGen)
import           Data.Function                               (($))
import           GHC.Generics                                (Par1 (..))
import           Prelude                                     (pure)
import qualified Prelude                                     as P
import           Test.Hspec                                  (Spec, describe)
import           Test.QuickCheck                             (Gen, withMaxSuccess, (===))
import           Tests.Symbolic.ArithmeticCircuit            (it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Algorithms.RSA
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Interpreter                 (Interpreter (Interpreter))

type I = Interpreter Fr

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x -! 1)

evalBool :: forall a . Bool (Interpreter a) -> a
evalBool (Bool (Interpreter (Par1 v))) = v

specRSA :: RandomGen g => g -> Spec
specRSA gen = do
    describe "RSA signature" $ do
        it "encrypts and decrypts correctly" $ withMaxSuccess 10 $ do
            msgBits <- toss $ (2 :: Natural) ^ (256 :: Natural)
            let (R.PublicKey{..}, R.PrivateKey{..}, _) = generateKeyPair gen (P.fromIntegral $ value @KeyLength)
                prvkey = PrivateKey (fromConstant private_d) (fromConstant public_n)
                pubkey = PublicKey (fromConstant public_e) (fromConstant public_n)
                msg = fromConstant msgBits

                sig = sign @I @256 msg prvkey
                check = verify @I @256 msg sig pubkey

            pure $ evalBool check === one

