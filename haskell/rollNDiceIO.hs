import System.Random

rollNDiceIO :: Int -> IO [Int]
rollNDiceIO n = sequence $ replicate n (randomRIO (1,6))
