class Integral a => Counter a where
    new :: a
    new = 0

    get :: a -> Int
    get = fromIntegral

    inc :: a -> a
    inc = (+1)


instance Counter Int where
    new = 1


add3 :: Counter a => a -> a
add3 = inc . inc . inc


