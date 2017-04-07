import Data.List (delete)

(\\) :: (Eq a) => [a] -> [a] -> [a]
xs \\ ys = foldl (\zs y -> delete y zs) xs ys

(//) :: (Eq a) => [a] -> [a] -> [a]
xs // ys = foldr (\y zs -> delete y zs) xs ys
