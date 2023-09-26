module ZkFold.Prelude where
    
import Prelude (Foldable, Num (..), Integer, foldl, error)

length :: Foldable t => t a -> Integer
length = foldl (\c _ -> c + 1) 0

take :: Integer -> [a] -> [a]
take 0 _ = []
take n (x:xs) = x : take (n - 1) xs
take _ [] = error "take: empty list"

drop :: Integer -> [a] -> [a]
drop 0 xs = xs
drop n (_:xs) = drop (n - 1) xs
drop _ [] = error "drop: empty list"