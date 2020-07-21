module  Replace
    (   (<-:)   -- 'y <-: x' is '[y/x]' 
    ,   replace
    )   where

(<-:) :: (Eq v) => v -> v -> (v -> v)
(<-:) y x u 
    | u == x    = y
    | otherwise = u


replace :: (Eq v) => v -> v -> (v -> v)
replace x y = (y <-: x) -- y in place of x
