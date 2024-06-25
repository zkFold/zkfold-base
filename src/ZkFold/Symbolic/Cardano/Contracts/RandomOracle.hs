module ZkFold.Symbolic.Cardano.Contracts.RandomOracle where

import           GHC.Generics ((:*:)(..), (:.:)(..), Par1(..))
import           Prelude                                        hiding (Bool, Eq (..), all, length, maybe, splitAt, zip,
                                                                 (!!), (&&), (*), (+), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        ((!!))
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (hash)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Data.Bool                      (Bool, Eq (..), Boolean (..))
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Types                          (Symbolic)

type Tokens = 2
type TxOut = Output Tokens ()
type TxIn  = Input Tokens ()
type Tx = Transaction 1 0 2 Tokens ()

type Sig a =
    ( StrictConv a (UInt 256 a)
    , MultiplicativeSemigroup (UInt 256 a)
    , Eq a (UInt 256)
    , MultiplicativeMonoid (UInt 64 a)
    , Eq a (UInt 64)
    , Iso (UInt 256 a) (ByteString 256 a)
    , Eq a (ByteString 224)
    , Extend (ByteString 224 a) (ByteString 256 a)
    , Eq a (ByteString 256)
    )

randomOracle
  :: forall a' a w. (Symbolic a, Sig a, FromConstant a' a, Foldable w)
  => a'
  -> Tx a
  -> w a
  -> Bool a
randomOracle c tx w =
    let -- The secret key is correct
        conditionSecretKey = Par1 (fromConstant c) == Par1 (hash w)

        -- Extracting information about the transaction
        seed                   = hash @a $ txiOutputRef $ unComp1 (txInputs tx) !! 0
        Comp1 vs               = txoTokens $ unComp1 (txOutputs tx) !! 0
        ValueElement p name n  = vs !! 1
        ValueElement{policyId} = unComp1 (txMint tx) !! 0

        -- Computing the random number
        r = hash (w :*: Par1 seed)

        -- The token's policy is correct
        conditionPolicyId  = p == policyId

        -- The token's name is correct
        conditionTokenName = name == ByteString (binaryExpansion r)

        -- The token's quantity is correct
        conditionQuantity  = n == one

    in conditionSecretKey && conditionPolicyId && conditionTokenName && conditionQuantity
