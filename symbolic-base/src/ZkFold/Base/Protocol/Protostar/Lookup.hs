module ZkFold.Base.Protocol.Protostar.Lookup where

import           Data.Map                                    (fromList, mapWithKey)
import           Data.These                                  (These (..))
import           Data.Zip
import           GHC.Generics
import           Prelude                                     hiding (Num (..), repeat, sum, zip, zipWith, (!!), (/),
                                                              (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Sparse.Vector              (SVector (..))
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))
import           ZkFold.Symbolic.MonadCircuit                (Arithmetic)

data ProtostarLookup (l :: Natural) (sizeT :: Natural)
    deriving Generic

data ProtostarLookupParams f sizeT = ProtostarLookupParams (Zp sizeT -> f) (f -> [Zp sizeT])
    deriving Generic

instance (Arithmetic f, KnownNat l, KnownNat sizeT) => SpecialSoundProtocol f (ProtostarLookup l sizeT) where
    type Witness f (ProtostarLookup l sizeT)         = Vector l f
    -- ^ w in the paper
    type Input f (ProtostarLookup l sizeT)           = ProtostarLookupParams f sizeT
    -- ^ t and t^{-1} from the paper
    type ProverMessage f (ProtostarLookup l sizeT)   = (Vector l f, SVector sizeT f)
    -- ^ (w, m) or (h, g) in the paper
    type VerifierMessage f (ProtostarLookup l sizeT) = f
    type VerifierOutput f (ProtostarLookup l sizeT)  = Bool

    type Degree (ProtostarLookup l sizeT)            = 2

    outputLength _ = value @l + (value @sizeT) + 1

    rounds :: ProtostarLookup l sizeT -> Natural
    rounds _ = 2

    -- TODO: It works only if the initial transcript is zero!!! Need to fix this
    prover :: ProtostarLookup l sizeT
           -> Witness f (ProtostarLookup l sizeT)
           -> Input f (ProtostarLookup l sizeT)
           -> f
           -> ProverMessage f (ProtostarLookup l sizeT)
    prover _ w (ProtostarLookupParams t invT) r =
        let m      = sum (SVector . fromList . (`zip` repeat one) . invT <$> w)
            h      = fmap (\w_i -> one // (w_i + r)) w
            g      = SVector $ mapWithKey (\i m_i -> m_i // (t i + r)) $ fromSVector m
        in if r == zero
            then (w, m)
            else (h, g)

    verifier :: ProtostarLookup l sizeT
             -> Input f (ProtostarLookup l sizeT)
             -> [ProverMessage f (ProtostarLookup l sizeT)]
             -> [f]
             -> Bool
    verifier _ (ProtostarLookupParams t _) [(w, m), (h, g)] [r, _] =
        let c1 = sum h == sum g
            c2 = all (== one) $ zipWith (*) h (fmap (+r) w)
            g' = SVector $ mapWithKey (\i g_i -> g_i * (t i + r)) $ fromSVector m
            f  = \case
                This _ -> False
                That _ -> False
                These x y -> x == y
            c3 = all (== one) $ alignWith f g' m
        in c1 && c2 && c3
    verifier _ _ _ _ = error "Invalid transcript"

