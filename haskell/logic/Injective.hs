module  Injective
    (   injective_on
    )   where


injective_on :: (Eq v, Eq w) => [v] -> (v -> w) -> Bool
injective_on xs f = all p [(x,y) | x <- xs, y <- xs] where
    p (x,y) = (f x /= f y) || (x == y)
