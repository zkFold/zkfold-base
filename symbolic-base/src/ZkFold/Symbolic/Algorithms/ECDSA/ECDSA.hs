{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}
module ZkFold.Symbolic.Algorithms.ECDSA.ECDSA where
import           Data.Type.Equality
import           GHC.Base                                (($))
import           GHC.TypeLits                            (KnownNat, Log2)
import qualified GHC.TypeNats

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field         (Zp, fromZp)
import           ZkFold.Base.Algebra.Basic.Number        (value)
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (BaseField, gen), Point (Inf, Point))
import qualified ZkFold.Symbolic.Class                   as S
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString         (ByteString)
import           ZkFold.Symbolic.Data.Combinators        (Iso (..), NumberOfRegisters, RegisterSize (Auto))
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement       (FieldElement)
import           ZkFold.Symbolic.Data.UInt               (UInt, eea)

ecdsaVerify :: forall curve p1 p2 c . (
    EllipticCurve curve
    , BaseField curve ~ Zp p1
    , KnownNat p2
    , Scale (ZkFold.Symbolic.Data.FieldElement.FieldElement c) (Point curve)
    , S.Symbolic c
    , Log2 (Order (S.BaseField c) GHC.TypeNats.- 1) ~ 255
    , SemiEuclidean (UInt 256 'Auto c)
    , KnownNat (NumberOfRegisters (S.BaseField c) 256 'Auto)
    )
    => Point curve
    -> ByteString 256 c
    -> (UInt 256 'Auto c, UInt 256 'Auto c)
    -> Bool c
ecdsaVerify publicKey message (r, s) = case c of
                Inf       -> false
                Point x _ -> r == (fromConstant (fromZp x) `mod` n)
    where
        n = fromConstant $ value @p2

        g = gen

        -- sInv ::UInt 256 'Auto c
        (sInv, _, _) = eea s n

        u = (from message * sInv) `mod` n

        v = r * sInv `mod` n

        c = (from u :: FieldElement c) `scale` g + (from v :: FieldElement c) `scale` publicKey
