factorial 0 = 1
factorial n = n * factorial (n - 1)



factorial' n = go 1 n 
  where
  go n 0  = n
  go n m  = go (n*m) (m-1) 
