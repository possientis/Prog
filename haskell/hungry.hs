newtype Hungry = Hungry { wrap:: (Int -> Hungry) }

f :: Int -> Hungry
f n = Hungry f

unwrap :: Hungry -> Int -> Hungry
unwrap (Hungry k) = k


f0 = f
f1 = unwrap $ f0 0
f2 = unwrap $ f1 0 

