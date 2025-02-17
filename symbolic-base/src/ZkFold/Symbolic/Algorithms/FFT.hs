{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Algorithms.FFT
    ( fft
    , ifft
    ) where

import           Control.DeepSeq                  (NFData, force)
import           Control.Monad                    (mapM)
import           Data.Maybe                       (fromJust)
import qualified Data.Vector                      as V
import           GHC.Generics                     (Generic)
import           Prelude                          (fmap, pure, ($), (.), (<$>))
import qualified Prelude                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.HFunctor        (hmap)
import           ZkFold.Base.Data.Vector          (Vector (..), toV)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool, (&&))
import           ZkFold.Symbolic.Data.ByteString  (ByteString)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators (Ceil, GetRegisterSize, Iso (..), KnownRegisters, NumberOfRegisters,
                                                   RegisterSize (..), Resize (..))
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Input       (SymbolicInput, isValid)
import           ZkFold.Symbolic.MonadCircuit     (MonadCircuit (..), newAssigned)

fft :: forall ctx n . (Symbolic ctx, KnownNat n) => ctx (Vector (2^n)) -> ctx (Vector (2^n))
fft v = hmap Vector $ fromCircuitF v (fft' (value @n) u . toV)
    where
        u :: BaseField ctx
        u = (fromJust $ rootOfUnity (value @n))

ifft :: forall ctx n . (Symbolic ctx, KnownNat n) => ctx (Vector (2^n)) -> ctx (Vector (2^n))
ifft v = hmap Vector $ fromCircuitF v $ \vec -> do
    unscaled <- fft' (value @n) u . toV $ vec
    mapM (\i -> newAssigned (\p -> scale nInv $ p i)) unscaled
    where
        u :: BaseField ctx
        u = (one // fromJust (rootOfUnity (value @n)))

        nInv :: BaseField ctx
        nInv = one // fromConstant ((2 :: Natural) ^ value @n)

fft'
    :: forall a i w m
    .  Arithmetic a
    => MonadCircuit i a w m
    => Natural
    -> a
    -> V.Vector i
    -> m (V.Vector i)
fft' 0 _ v = pure v
fft' n wn v = do
    a0Hat <- fft' (n -! 1) wn2 a0
    a1Hat <- fft' (n -! 1) wn2 a1
    V.generateM (P.fromIntegral $ (2 :: Natural) ^ n) $ \ix -> do
        let arrIx = ix `P.mod` halfLen

            op :: AdditiveGroup p => p -> p -> p
            op = if ix P.< halfLen then (+) else (-)

            a0k = a0Hat `V.unsafeIndex` arrIx
            a1k = a1Hat `V.unsafeIndex` arrIx
            wnp = wn ^ (P.fromIntegral arrIx :: Natural)
        newAssigned $ \p -> p a0k `op` scale wnp (p a1k)
    where
        a0 = V.ifilter (\i _ -> i `P.mod` 2 P.== 0) v
        a1 = V.ifilter (\i _ -> i `P.mod` 2 P.== 1) v

        wn2 = wn * wn

        halfLen = P.fromIntegral $ (2 :: Natural) ^ (n -! 1)
