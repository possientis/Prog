gcd' :: (Integral a) => a -> a -> a
gcd' a b = if b == 0 then a else gcd' b (mod a b)
