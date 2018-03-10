import Prelude hiding (id,map)

{-# INLINE foo #-}
{-# NOINLINE bar #-}


id :: a -> a
id x = x


idInt :: Int -> Int
idInt = id

compose :: (b -> c) -> (a -> b) -> (a -> c)
compose g f x = g (f x)

map :: (a -> b) -> [a] -> [b]
map f  []        = []
map f  (x:xs)    = (f x) : map f xs

test x y = x `seq` y


f 0 = 1
f 1 = 2
f 2 = 3
f 3 = 4
f 4 = 5
f _ = 0


foo :: (a -> b -> c) -> a -> b -> c
foo f x y = f x y

bar :: (a -> b -> c) -> a -> b -> c
bar f x y = f x y 

test1 :: Int
test1 = foo (+) 10 20

test2 :: Int
test2 = bar (+) 20 30
