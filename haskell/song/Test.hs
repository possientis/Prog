r :: Double
r = -29.953087149481938

k :: Integer
k = 9

main :: IO ()
main = do
    let x = r ^ k
    let y =  1 / ((1 / r) ^ k)
    let d = abs (x - y)
    putStrLn $ "|x - y| = " ++ show d

