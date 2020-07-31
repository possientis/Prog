module  Coincide
    (   coincide
    )   where

coincide :: (Eq w) => [v] -> (v -> w) -> (v -> w) -> Bool
coincide xs f g = all p xs where p x = (f x == g x)
