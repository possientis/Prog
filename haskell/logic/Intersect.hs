module  Intersect
    (   inter
    )   where

inter :: (Eq a) => [a] -> [a] -> [a]
inter [] _          = []
inter (x : xs)  ys  = if x `elem` ys then x : inter xs ys else inter xs ys
