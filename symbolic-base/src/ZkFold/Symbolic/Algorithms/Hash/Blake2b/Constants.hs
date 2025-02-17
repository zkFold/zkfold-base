{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Algorithms.Hash.Blake2b.Constants ( blake2b_iv, sigma ) where

import           GHC.IsList                      (IsList (..))
import           Numeric.Natural                 (Natural)
import           Prelude                         (Int, map, type (~), ($), (<$>))

import           ZkFold.Base.Algebra.Basic.Class (FromConstant (..))

-- | Initialization Vector (same as for SHA-512)
blake2b_iv :: (FromConstant Natural x, IsList (v x), Item (v x) ~ x) => v x
blake2b_iv = fromList $ fromConstant @Natural <$>
    [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
      0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ]

{-
          Round    |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
        -----------+-------------------------------------------------+
         SIGMA[0]  |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
         SIGMA[1]  | 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3 |
         SIGMA[2]  | 11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4 |
         SIGMA[3]  |  7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8 |
         SIGMA[4]  |  9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13 |
         SIGMA[5]  |  2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9 |
         SIGMA[6]  | 12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11 |
         SIGMA[7]  | 13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10 |
         SIGMA[8]  |  6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5 |
         SIGMA[9]  | 10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0 |
         SIGMA[10] |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
         SIGMA[11] | 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3 |
        -----------+-------------------------------------------------+
-}

sigma :: forall v .
       ( IsList (v Int)
       , IsList (v (v Int))
       , Item (v Int) ~ Int
       , Item (v (v Int)) ~ v Int
       ) => v (v Int)
sigma = fromList $ map fromList [
           [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ],
           [ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 ],
           [ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 ],
           [ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 ],
           [ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 ],
           [ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 ],
           [ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 ],
           [ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 ],
           [ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 ],
           [ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 ],
           [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ],
           [ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 ]
       ]
