{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Examples.MiMCHash (exampleMiMC) where

import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), (!!), any)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (fromR1CS)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..))
import           ZkFold.Crypto.Data.Conditional              (bool)
import           ZkFold.Prelude                              ((!!))

import           Examples.MiMC.Constants                     (mimcConstants)
import           Tests.Utility.Types                         (R, I)

mimcHash :: forall a . (FiniteField a, FromConstant I a) =>
    Integer -> a -> a -> a -> a
mimcHash nRounds k xL xR = 
    let c  = mimcConstants !! (nRounds-1)
        t5 = (xL + k + c) ^ (5 :: Integer)
    in bool (xR + t5) (mimcHash (nRounds-1) k (xR + t5) xL) (nRounds > 1)
          
exampleMiMC :: IO ()
exampleMiMC = do
    let nRounds = 220

    -- TODO: change the type application to build an arithmetization for the correct field
    let r = compile @R (mimcHash @R nRounds zero)

    putStrLn "\nStarting MiMC test...\n"

    putStrLn "MiMC hash function"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (r1csSizeN r)
    putStrLn $ "Number of variables: " ++ show (r1csSizeM r)

    putStrLn "\nR1CS polynomials:\n"
    print $ fromR1CS r