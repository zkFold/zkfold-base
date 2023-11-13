module ZkFold.Base.Algebra.EllipticCurve.BLS12_381 where

import           Prelude                           hiding (Num(..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.Class

data BLS12_381

data BLS12_381_BaseField
instance Finite BLS12_381_BaseField where
    order = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
instance Prime BLS12_381_BaseField

type instance BaseField BLS12_381 = Zp BLS12_381_BaseField

data BLS12_381_Scalar
instance Finite BLS12_381_Scalar where
    order = 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance Prime BLS12_381_Scalar

type instance ScalarField BLS12_381 = Zp BLS12_381_Scalar

instance EllipticCurve BLS12_381 where
    inf = Inf

    gen = Point
        3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
        1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569

    add = addPoints

    mul = pointMul