module  Difference
    (   (\\)
    )   where

(\\) :: (Eq a) => [a] -> [a] -> [a]
(\\) [] _        = []
(\\) (x : xs) ys = if x `elem` ys then xs \\ ys else x : xs \\ ys 

