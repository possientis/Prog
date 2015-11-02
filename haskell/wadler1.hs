import Test.QuickCheck
sum1 = sum [1,2,3]
sum2 = sum [x*x | x <- [1,2,3], odd x]
prod1 = product [1,2,3,4]
prod2 = product []
fact n = product [1..n]
squares :: [Integer] -> [Integer]
squares xs = [x*x | x <- xs]
squares' [] =[]
squares' (x:xs) = x*x : squares' xs
