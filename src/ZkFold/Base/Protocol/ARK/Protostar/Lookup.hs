module ZkFold.Base.Protocol.ARK.Protostar.Lookup where

import           Data.ByteString                              (ByteString)
import           Data.Kind                                    (Type)
import           Data.Map                                     (fromList, mapWithKey)
import           Data.These                                   (These(..))
import           Data.Typeable                                (Typeable)
import           Data.Zip
import           Prelude                                      hiding (zip, repeat, (/), sum, Num (..), (^), (!!), zipWith)
import           Test.QuickCheck                              (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Data.ByteString                  (ToByteString, FromByteString)
import           ZkFold.Base.Data.Sparse.Vector               (SVector(..))
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Base.Protocol.NonInteractiveProof     (NonInteractiveProof (..), transcript, challenge)

data ProtostarLookup (l :: Type) (sizeT :: Type) (f :: Type)

data ProtostarLookupParams sizeT f = ProtostarLookupParams (Zp sizeT -> f) (f -> [Zp sizeT])
instance Show (ProtostarLookupParams sizeT f) where
    show _ = "ProtostarLookupParams"
instance AdditiveMonoid f => Arbitrary (ProtostarLookupParams sizeT f) where
    arbitrary = return $ ProtostarLookupParams (const zero) (const [])

instance (Finite l, Finite sizeT, Typeable l, Typeable sizeT, Typeable f, Show f, Arbitrary f,
    ToByteString f, FromByteString f, FiniteField f, Eq f)
        => NonInteractiveProof (ProtostarLookup l sizeT f) where
    type Transcript (ProtostarLookup l sizeT f)   = ByteString
    type Params (ProtostarLookup l sizeT f)       = ProtostarLookupParams sizeT f
    -- ^ t and t^{-1} from the paper
    type SetupSecret (ProtostarLookup l sizeT f)  = ()
    type Setup (ProtostarLookup l sizeT f)        = ProtostarLookupParams sizeT f
    -- ^ same as Params
    type ProverSecret (ProtostarLookup l sizeT f) = ()
    type Witness (ProtostarLookup l sizeT f)      = Vector l f
    -- ^ w in the paper
    type Input (ProtostarLookup l sizeT f)        = ()
    type Proof (ProtostarLookup l sizeT f)        = (Vector l f, SVector sizeT f, Vector l f, SVector sizeT f)
    -- ^ (w, m, h, g) in the paper

    setup :: Params (ProtostarLookup l sizeT f) -> SetupSecret (ProtostarLookup l sizeT f) -> Setup (ProtostarLookup l sizeT f)
    setup p _ = p

    prove :: ProverSecret (ProtostarLookup l sizeT f)
          -> Setup (ProtostarLookup l sizeT f)
          -> Witness (ProtostarLookup l sizeT f)
          -> (Input (ProtostarLookup l sizeT f), Proof (ProtostarLookup l sizeT f))
    prove _ (ProtostarLookupParams t invT) w =
        let m      = sum (SVector . fromList . (`zip` repeat one) . invT <$> w)
            (r, _) = challenge $ (mempty :: ByteString) `transcript` (w, m)
            h      = fmap (\w_i -> one / (w_i + r)) w
            g      = SVector $ mapWithKey (\i m_i -> m_i / (t i + r)) $ fromSVector m
        in ((), (w, m, h, g))

    verify :: Setup (ProtostarLookup l sizeT f) -> Input (ProtostarLookup l sizeT f) -> Proof (ProtostarLookup l sizeT f) -> Bool
    verify (ProtostarLookupParams t _) _ (w, m, h, g) =
        let (r, _) = challenge $ (mempty :: ByteString) `transcript` (w, m)
            c1 = sum h == sum g
            c2 = all (== one) $ zipWith (*) h (fmap (+r) w)
            g' = SVector $ mapWithKey (\i g_i -> g_i * (t i + r)) $ fromSVector m
            f  = \case
                This _ -> False
                That _ -> False
                These x y -> x == y
            c3 = all (== one) $ alignWith f g' m
        in c1 && c2 && c3