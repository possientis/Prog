inc :: Int -> Int
inc n = n+1

mult :: (Int,Int) -> Int
mult (n,m) = n*m

myMult = \x -> \y -> x*y

inf = 1 + inf

ones = 1:ones

list :: Int -> [Int]
list 0 = [2..]
list n = [x | l <- [list (n-1)]
            , y <- [l !! (n-1)]
            , x <- l
            , mod x y /= 0 || x == y]

-- Prime numbers

sieve (p:xs) = p:sieve [x | x <- xs, mod x p /= 0]
primes = sieve [2..]

sieve' (p:xs) = p : sieve' (filter (\x -> mod x p /= 0) xs)
primes' = sieve' [2..]

-- inefficient
sumWith v [] = v
sumWith v (x:xs) = sumWith (v+x) xs

sumWith' v [] = v
sumWith' v (x:xs) = (sumWith' $!(v+x)) xs   -- forces evaluation

