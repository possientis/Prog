fib = 1:1:zipWith(+) fib(tail fib)

data List a = a:(List a)|[]
listMerge::List Int->List Int->List Int
listMerge [] [] = []
listMerge a [] = a
listMerge [] b = b
listMerge (a:as) (b:bs) = if a < b
  then a:listMerge as (b:bs)
  else b:listMerge (a:as) bs

main = putStrLn "Hello world!"
