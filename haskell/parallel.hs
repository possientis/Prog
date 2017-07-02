import Control.Parallel.Strategies


f = id :: Int -> Int

test :: Int -> Int -> (Int,Int)
test x y = runEval $ do
    a <- rpar (f x)
    b <- rseq (f y)
    rseq a
    return (a,b)


main = do
    putStrLn $ show $ test 3 4


