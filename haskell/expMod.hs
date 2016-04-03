-- powerMod p x y = x^y mod p
expMod :: Integer -> Integer -> Integer -> Integer
expMod p x y = loop p x y 1 where
  loop p x y prod
    | y == 0  = mod prod p
    | even y  = loop p (mod (x*x) p) (div y 2) prod
    | odd  y  = loop p x (y -1) (mod (prod*x) p)
    | otherwise = error "expMod: unexpected error"
 
