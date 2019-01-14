module  Permute
    (   permute
    )
    where

permute :: (Eq v) => v -> v -> v -> v
permute x y u 
    | u == x    = y
    | u == y    = x
    | otherwise = u
