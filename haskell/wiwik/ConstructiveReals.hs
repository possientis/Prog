import Data.Number.CReal -- libghc-numbers-dev

-- algebraic
phi :: CReal
phi = (1 + sqrt 5)/2

-- transcendental
ramanujan :: CReal
ramanujan = exp (pi * sqrt 163)


main :: IO ()
main = do
    putStrLn $ showCReal 60 pi
    putStrLn $ showCReal 60 phi
    putStrLn $ showCReal 43 ramanujan
