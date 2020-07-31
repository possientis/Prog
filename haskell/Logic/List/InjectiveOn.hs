module  List.InjectiveOn
    (   injectiveOn
    )   where


injectiveOn :: (Eq v, Eq w) => [v] -> (v -> w) -> Bool
injectiveOn xs f = all p [(x,y) | x <- xs, y <- xs] where
    p (x,y) = (f x /= f y) || (x == y)
