{-# LANGUAGE RankNTypes     #-}
{-
applyToFive :: forall a . (a -> a) -> Int
applyToFive f = f 5
-}


applyToFive :: (forall a . a -> a) -> Int
applyToFive f = f 5

x1 :: Int
x1 = applyToFive id

-- f has no polymorphic parameter : rank 0
f0 :: Integer -> Double
f0 = fromInteger

-- f1 is const : rank 1
f1 :: forall a b. a -> b -> a
f1 x _ = x

-- g1 is head : rank 1
g1 :: forall a . [a] -> a
g1 []      = error "empty list"
g1 (x : _) = x

-- f2 has a rank 1 parameter : rank 2 
f2 :: (forall a . a -> a) -> Int
f2 = applyToFive

-- g2 has a rank 1 parameter : rank 2
g2 :: forall r . (forall a . a -> r) -> r
g2 f = f (5 :: Int)

-- no polymorphic parameter  : rank 0 ?
g0 :: Int -> forall a . a -> a
g0 _ = id

-- h2 has a rank 1 parameter : rank 2
h2 :: (a -> b) -> (forall c . c -> a) -> b
h2 f g = f $ g (5 :: Int)


fx :: ((forall x . m x -> b (z m x)) -> b (z m a)) -> m a
fx f = undefined

