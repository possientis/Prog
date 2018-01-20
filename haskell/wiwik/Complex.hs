import Data.Complex

{-
data Complex a = a :+ a

mkPolar :: RealFloat a => a -> a -> Complex a
-}


ex1 :: Complex Integer
ex1 = 0 :+ 1

ex2 = (0 :+ 1) + (1 :+ 0)
-- 1.0 :+ 1.0

ex3 :: Complex Double
ex3 = exp (0 :+ 2*pi)
-- 1.0 :+ (-2.4492935982947064e-16)


ex4 :: Complex Double
ex4 = mkPolar 1 (2*pi)
-- 1.0 :+ (-2.4492935982947064e-16)


f :: Double -> Int -> Complex Double
f x n = (cos x :+ sin x)^n

g :: Double -> Int -> Complex Double
g x n' = cos (n*x) :+ sin (n*x) where 
    n = fromIntegral n'
