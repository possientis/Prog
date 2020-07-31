module  List.Include
    (   (<==)
    )   where

infix 3 <==

(<==)  :: (Eq a) => [a] -> [a] -> Bool
(<==)  xs ys = all (`elem` ys) xs
