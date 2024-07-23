module Examples.ReverseList (exampleReverseList) where

import           ZkFold.Base.Data.Vector (Vector, reverse)

-- | Reverses the order of elements in a vector
exampleReverseList :: Vector n t -> Vector n t
exampleReverseList = reverse
