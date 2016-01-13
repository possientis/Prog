digits = [1,2,3,4,5,6,7,8,9]

permutations = partial 9 where
  partial 1 = [[x] | x <- digits]
  partial n = [(x:xs)|xs <- partial (n - 1), x <- digits, not (elem x xs)]

isSolution [u,v,w,x,y,z,t,r,s] 
  = ((u*10 + v)*w ==  (x*10 + y) && (x*10 + y) + (z*10 + t) == r*10 + s)

main = putStrLn (show (filter isSolution permutations))
