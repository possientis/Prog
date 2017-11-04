{-# LANGUAGE BangPatterns #-}

-- don't get it

f :: (a,b) -> Int
f (a,b) = const 1 a

g :: (a,b) -> Int
g (!a,b) = const 1 a 


test1 :: Int
test1 = f (error "a", error "b")  -- 1

test2 :: Int
test2 = g (error "a", error "b") -- error "a"
