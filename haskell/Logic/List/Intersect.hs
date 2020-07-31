module  List.Intersect
    (   (/\)
    )   where

(/\) :: (Eq a) => [a] -> [a] -> [a]
(/\) [] _          = []
(/\) (x : xs)  ys  = if x `elem` ys then x : xs /\ ys else xs /\ ys

