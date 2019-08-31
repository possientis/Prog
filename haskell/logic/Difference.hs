module  Difference
    (   diff
    )   where

diff :: (Eq a) => [a] -> [a] -> [a]
diff [] _        = []
diff (x : xs) ys = if x `elem` ys then diff xs ys else x : diff xs ys 
