factorial 0 = 1
factorial n = n * factorial (n - 1)



factorial' n = go n 1
  where
  go 0 n  = n
  go m n  = go (m-1) (n*m) 
