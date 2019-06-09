module  Haskell.Permute
    (   (<->)   -- 'x <-> y' is '[x:y]'
    ,   permute
    )   where


(<->) :: (Eq v) => v -> v -> (v -> v)
(<->) x y u 
    | u == x    = y
    | u == y    = x
    | otherwise = u


permute :: (Eq v) => v -> v -> (v -> v)
permute = (<->)
