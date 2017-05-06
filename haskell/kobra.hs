import Prelude hiding (reverse)

reverse :: [a] -> [a]
reverse = go [] where
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
    
    
main = do
    print $ reverse [1..20]
