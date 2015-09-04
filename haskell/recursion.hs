factorial :: Int -> Int
factorial n = product [1..n]
myFact :: Int -> Int
myFact n = product (take n [1..])
myProduct ::Num a => [a] -> a
myProduct [] = 1
myProduct (x:xs) = x*myProduct(xs)
yourFact :: Int -> Int
yourFact 0 = 1
yourFact n  = n * yourFact (n - 1)
myLength :: [a] -> Int
myLength [] = 0
myLength (_:xs) = 1 + myLength xs
myReverse :: [a] -> [a]
myReverse [] = []
myReverse (x:xs) = myReverse xs ++ [x]
myZip :: [a] -> [b] -> [(a,b)]
myZip [] _ = []
myZip _ [] = []
myZip (x:xs) (y:ys) = (x,y) : myZip xs ys
-- This is a comment
myDrop :: Int -> [a] -> [a] -- This is another comment
myDrop 0 xs = xs
myDrop n [] = []
myDrop n (_:xs) = myDrop (n-1) xs
(£) :: [a] -> [a] -> [a]
[] £ ys = ys
(x:xs) £ ys = x : (xs £ ys)
-- qsort :: [Int] -> [Int]
qsort [] = []
qsort (x:xs) =
  qsort smaller ++ [x] ++ qsort larger
  where
    smaller = [a | a <- xs, a <= x]
    larger  = [b | b <- xs, x <  b]

f :: Int -> Int
f x = n * x where n = 2
