module Tests.Base.Algebra.Univariate (specUnivariate) where

import           Prelude
import           Tests.Base.Algebra.Univariate.Poly    (specUnivariatePoly)
import           Tests.Base.Algebra.Univariate.PolyVec (specUnivariatePolyVec)

specUnivariate :: IO ()
specUnivariate = do
    specUnivariatePoly
    specUnivariatePolyVec
