module Tests.Poly (testPoly) where
import           Prelude                                    hiding (not, Num(..), Eq(..), (^), (/))

testPoly :: IO ()
testPoly = do
    putStrLn "\nStarting Poly test...\n"