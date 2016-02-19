

sol1 = [(x,y) | x <- [1..9], y <- [1..9], x * y == 24, x+y == 10, x <= y]

digits = [0,1,2,3,4,5,6,7,8,9]
range 1 = [[x] | x <- digits ]
range n = [x:xs | xs <- range (n-1), x <- digits, not (elem x xs)]
from = [(a,b,c,d,e,f,g,h) | [a,b,c,d,e,f,g,h] <- range 8]

sol2 = [(s*1000 + e*100 + n*10 + d, m*1000 + o*100 + r*10 + e, m*10000 + o*1000 + n*100 + e*10 + y) |
          (s,e,n,d,m,o,r,y) <- from,
          s /= 0,
          m /= 0,
          s*1000 + e*100 + n*10 + d + m*1000 + o*100 + r*10 + e == m*10000 + o*1000 + n*100 + e*10 + y]

main = do
  putStrLn (show sol2)
