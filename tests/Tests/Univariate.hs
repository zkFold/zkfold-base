module Tests.Univariate (specUnivariate) where

import           Prelude
import           Tests.Univariate.Poly    (specUnivariatePoly)
import           Tests.Univariate.PolyVec (specUnivariatePolyVec)

specUnivariate :: IO ()
specUnivariate = do
    specUnivariatePoly
    specUnivariatePolyVec
