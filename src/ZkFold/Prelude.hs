module ZkFold.Prelude where
    
import Prelude (Foldable, Num (..), Integer, foldl)

length :: Foldable t => t a -> Integer
length = foldl (\c _ -> c + 1) 0