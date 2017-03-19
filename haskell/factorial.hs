
-- not tail recursive
factorial 0 = 1
factorial n = n * factorial (n - 1)


-- tail recursive but lazy, so probably not much better
factorial' n = go n 1
  where
  go 0 n  = n
  go m n  = go (m-1) (n*m) 

factorial'' n = product [1..n]
