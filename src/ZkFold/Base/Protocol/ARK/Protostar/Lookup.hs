{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.Lookup where

import           Data.Functor.Rep                                (mzipWithRep)
import           Data.Map                                        (fromList, mapWithKey)
import           Data.These                                      (These (..))
import           Data.Zip
import           Numeric.Natural                                 (Natural)
import           Prelude                                         hiding (Num (..), repeat, sum, zip, zipWith, (!!), (/),
                                                                  (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate    (Polynomial')
import           ZkFold.Base.Data.Sparse.Vector                  (SVector (..))
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol (..), SpecialSoundTranscript)
import           ZkFold.Symbolic.Compiler                        (Arithmetic)

data ProtostarLookup (l :: Natural) (sizeT :: Natural)

data ProtostarLookupParams f sizeT = ProtostarLookupParams (Zp sizeT -> f) (f -> [Zp sizeT])

instance (Arithmetic f, KnownNat sizeT, KnownNat l) => SpecialSoundProtocol f (ProtostarLookup l sizeT) where
    type Witness f (ProtostarLookup l sizeT)         = Vector l f
    -- ^ w in the paper
    type Input f (ProtostarLookup l sizeT)           = ProtostarLookupParams f sizeT
    -- ^ t and t^{-1} from the paper
    type ProverMessage t (ProtostarLookup l sizeT)   = (Vector l t, SVector sizeT t)
    -- ^ (w, m) or (h, g) in the paper
    type VerifierMessage t (ProtostarLookup l sizeT) = t

    type Dimension (ProtostarLookup l sizeT)         = l + sizeT + 1
    type Degree (ProtostarLookup l sizeT)            = 2

    rounds :: ProtostarLookup l sizeT -> Natural
    rounds _ = 2

    prover :: ProtostarLookup l sizeT
           -> Witness f (ProtostarLookup l sizeT)
           -> Input f (ProtostarLookup l sizeT)
           -> SpecialSoundTranscript f (ProtostarLookup l sizeT)
           -> ProverMessage f (ProtostarLookup l sizeT)
    prover _ w (ProtostarLookupParams _ invT) [] =
        let m      = sum (SVector . fromList . (`zip` repeat one) . invT <$> w)
        in (w, m)
    prover _ _ (ProtostarLookupParams t _) [((w, m), r)] =
        let h      = fmap (\w_i -> one // (w_i + r)) w
            g      = SVector $ mapWithKey (\i m_i -> m_i // (t i + r)) $ fromSVector m
        in (h, g)
    prover _ _ _ _ = error "Invalid transcript"

    -- TODO: implement this
    verifier' :: ProtostarLookup l sizeT
              -> Input f (ProtostarLookup l sizeT)
              -> SpecialSoundTranscript Natural (ProtostarLookup l sizeT)
              -> Vector (Dimension (ProtostarLookup l sizeT)) (Polynomial' f)
    verifier' = undefined

    verifier :: ProtostarLookup l sizeT
             -> Input f (ProtostarLookup l sizeT)
             -> SpecialSoundTranscript f (ProtostarLookup l sizeT)
             -> Bool
    verifier _ (ProtostarLookupParams t _) [((w, m), r), ((h, g), _)] =
        let c1 = sum h == sum g
            c2 = all (== one) $ mzipWithRep (*) h (fmap (+r) w)
            g' = SVector $ mapWithKey (\i g_i -> g_i * (t i + r)) $ fromSVector m
            f  = \case
                This _ -> False
                That _ -> False
                These x y -> x == y
            c3 = all (== one) $ alignWith f g' m
        in c1 && c2 && c3
    verifier _ _ _ = error "Invalid transcript"

