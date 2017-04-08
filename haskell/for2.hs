l = [i | i <- [1..1000], mod i 2 /= 0, mod i 3 /= 0]

m = proc 1000 [] p where
  proc 0 xs  p = xs
  proc n xs  p = if p n then proc (n-1) (n:xs) p else proc (n-1) xs p
  p n = and [mod n 2 /= 0, mod n 3 /= 0]

myMap f = foldr (\x -> \y -> (f x) : y) []
