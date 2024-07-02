module ZkFold.Symbolic.Algorithms.Hash.Blake2b.Constants ( blake2b_iv, sigma ) where

import qualified Data.Vector                     as V
import           Numeric.Natural                 (Natural)
import           Prelude                         (Int, ($), (<$>))

import           ZkFold.Base.Algebra.Basic.Class (FromConstant (..))
import           ZkFold.Symbolic.Data.UInt       (UInt)
-- | Initialization Vector.
blake2b_iv :: FromConstant Natural (UInt 64 b a) => V.Vector (UInt 64 b a)
blake2b_iv = V.fromList $ fromConstant @Natural <$> [
       0x6A09E667F3BCC908, 0xBB67AE8584CAA73B,
       0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
       0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
       0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

sigma :: V.Vector (V.Vector Int)
sigma = V.fromList [
           V.fromList [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ],
           V.fromList [ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 ],
           V.fromList [ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 ],
           V.fromList [ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 ],
           V.fromList [ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 ],
           V.fromList [ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 ],
           V.fromList [ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 ],
           V.fromList [ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 ],
           V.fromList [ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 ],
           V.fromList [ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 ],
           V.fromList [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ],
           V.fromList [ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 ]]
