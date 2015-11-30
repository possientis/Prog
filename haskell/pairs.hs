pairs :: Int -> [(Int,Int)]
pairs n = [(i,j) | i <- [1..n], j <- [(i+1)..n]]

-- do notation for list monad... go figure
pairs' :: Int -> [(Int,Int)]
pairs' n = do {
  i <- [1..n];
  j <- [(i+1)..n];
  return (i,j)
}

guard :: Bool -> [()]
guard False = []
guard True = [()]

pairs'' :: Int -> [(Int,Int)]
pairs'' n = [(i,j) | i <- [1..n], j <- [1..n], i < j]

pairs''' :: Int -> [(Int,Int)]
pairs''' n = do {
  i <- [1..n];
  j <- [1..n];
  guard (i < j); -- no idea why this is working
  return (i,j)
}
