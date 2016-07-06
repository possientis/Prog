import System.Random

rand :: IO Int
rand = getStdRandom(randomR (0,100))


