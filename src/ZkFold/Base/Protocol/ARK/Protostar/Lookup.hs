module ZkFold.Base.Protocol.ARK.Protostar.Lookup where

import           Data.Kind                                       (Type)
import           Data.Map                                        (fromList, mapWithKey)
import           Data.These                                      (These(..))
import           Data.Zip
import           Prelude                                         hiding (zip, repeat, (/), sum, Num (..), (^), (!!), zipWith)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Data.Sparse.Vector                  (SVector(..))
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)

data ProtostarLookup (l :: Type) (sizeT :: Type) (f :: Type)

data ProtostarLookupParams sizeT f = ProtostarLookupParams (Zp sizeT -> f) (f -> [Zp sizeT])

instance (Finite sizeT, Eq f, FiniteField f) => SpecialSoundProtocol (ProtostarLookup l sizeT f) where
    type Witness (ProtostarLookup l sizeT f)         = Vector l f
    -- ^ w in the paper
    type Input (ProtostarLookup l sizeT f)           = ProtostarLookupParams sizeT f
    -- ^ t and t^{-1} from the paper
    type ProverMessage (ProtostarLookup l sizeT f)   = (Vector l f, SVector sizeT f)
    -- ^ (w, m) or (h, g) in the paper
    type VerifierMessage (ProtostarLookup l sizeT f) = f

    rounds :: Integer
    rounds = 2

    prover :: ProtostarLookup l sizeT f
           -> Witness (ProtostarLookup l sizeT f)
           -> Input (ProtostarLookup l sizeT f)
           -> SpecialSoundTranscript (ProtostarLookup l sizeT f)
           -> ProverMessage (ProtostarLookup l sizeT f)
    prover _ w (ProtostarLookupParams _ invT) [] =
        let m      = sum (SVector . fromList . (`zip` repeat one) . invT <$> w)
        in (w, m)
    prover _ _ (ProtostarLookupParams t _) [((w, m), r)] =
        let h      = fmap (\w_i -> one / (w_i + r)) w
            g      = SVector $ mapWithKey (\i m_i -> m_i / (t i + r)) $ fromSVector m
        in (h, g)
    prover _ _ _ _ = error "Invalid transcript"

    verifier :: ProtostarLookup l sizeT f
             -> Input (ProtostarLookup l sizeT f)
             -> SpecialSoundTranscript (ProtostarLookup l sizeT f)
             -> Bool
    verifier _ (ProtostarLookupParams t _) [((w, m), r), ((h, g), _)] =
        let c1 = sum h == sum g
            c2 = all (== one) $ zipWith (*) h (fmap (+r) w)
            g' = SVector $ mapWithKey (\i g_i -> g_i * (t i + r)) $ fromSVector m
            f  = \case
                This _ -> False
                That _ -> False
                These x y -> x == y
            c3 = all (== one) $ alignWith f g' m
        in c1 && c2 && c3
    verifier _ _ _ = error "Invalid transcript"