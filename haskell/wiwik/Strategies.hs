import Control.Parallel.Strategies

-- ghc -threaded -rtsopts -o a.out Strategies.hs
-- time ./a.out +RTS -N2 
-- dont see any time improvement: (

parPair' :: Strategy (a,b)
parPair' (a,b) = do
    a' <- rpar a
    b' <- rpar b
    return (a',b')


fib :: Int -> Int 
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

serial :: (Int, Int)
serial = (fib 33, fib 34)

parallel :: (Int, Int)
parallel = runEval . parPair' $ (fib 33, fib 34)

main :: IO ()
main = do
    print parallel
