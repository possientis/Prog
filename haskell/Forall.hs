{-# LANGUAGE ExplicitForAll #-}

example1 :: forall a. [a]
example1 = []


example2 :: forall a. [a]
example2 = [undefined]

map' :: forall a. forall b. (a -> b) -> [a] -> [b]  
map' f = foldr ((:) . f) []

reverse' :: forall a. [a] -> [a]
reverse' = foldl (flip (:)) []
