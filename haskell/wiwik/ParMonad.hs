import Control.Monad
import Control.Monad.Par

f,g :: Int -> Int
f x = x + 10
g x = x * 10

-- f x      g x
--   \     /
--    a + b 
--   /    \
--f (a+b) g (a+b)
--   \     /
--     (d,e)

ex1 :: Int -> (Int,Int)
ex1 x = runPar $ do
    [a,b,c,d,e] <- replicateM 5 new
    fork (put a (f x))
    fork (put b (g x))
    a' <- get a
    b' <- get b
    fork (put c (a' + b'))
    c' <- get c
    fork (put d (f c'))
    fork (put e (g c'))
    d' <- get d
    e' <- get e
    return (d', e')


ex2 :: [Int]
ex2 = runPar $ do
    xs <- parMap (+1) [1..25]
    return xs


ex3 :: Int -> Int
ex3 n = runPar $ do
    let range = (InclusiveRange 1 n)
    let mapper x = return (x^2)
    let reducer x y = return (x + y)
    parMapReduceRangeThresh 10 range mapper reducer 0
