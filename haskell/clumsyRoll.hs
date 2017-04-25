import System.Random

clumsyRollDice :: (Int, Int)
clumsyRollDice = (n, m) where
  (n, g) = randomR (1,6) (mkStdGen 0)
  (m, _) = randomR (1,6) g

rollDice :: StdGen -> ((Int, Int), StdGen)
rollDice g0 = ((n,m), g2) where
  (n, g1) = randomR (1,6) g0
  (m, g2) = randomR (1,6) g1
