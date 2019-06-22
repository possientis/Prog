module  Include
    (   incl
    )   where

incl :: (Eq a) => [a] -> [a] -> Bool
incl xs ys = all (`elem` ys) xs
