module ZkFold.Prelude where
    
import           Data.Aeson           (ToJSON, encode, FromJSON, decode)
import           Data.ByteString.Lazy (writeFile, readFile)
import           Prelude              hiding ((!!), take, drop, replicate, writeFile, readFile)

length :: Foldable t => t a -> Integer
length = foldl (\c _ -> c + 1) 0

take :: Integer -> [a] -> [a]
take 0 _ = []
take n (x:xs) = x : take (n - 1) xs
take _ [] = error "ZkFold.Prelude.take: empty list"

drop :: Integer -> [a] -> [a]
drop 0 xs = xs
drop n (_:xs) = drop (n - 1) xs
drop _ [] = error "ZkFold.Prelude.drop: empty list"

splitAt :: Integer -> [a] -> ([a], [a])
splitAt n xs = (take n xs, drop n xs)

replicate :: Integer -> a -> [a]
replicate 0 _ = []
replicate n x = x : replicate (n - 1) x

(!!) :: [a] -> Integer -> a
_      !! i | i < 0 = error "ZkFold.Prelude.!!: negative index"
[]     !! _         = error "ZkFold.Prelude.!!: index too large"
(x:xs) !! i         = if i == 0 then x else xs !! (i-1)

writeFileJSON :: ToJSON a => FilePath -> a -> IO ()
writeFileJSON file = writeFile file . encode

readFileJSON :: FromJSON a => FilePath -> IO a
readFileJSON file = do
    content <- readFile file
    case decode content of
        Nothing -> error "ZkFold.Prelude.readFileJSON: invalid JSON"
        Just x  -> return x