import Control.Monad

pythags = [ (x,y,z) | z <- [1..], x <- [1..z], y <- [x..z], x^2 + y^2 == z^2 ]


pythags' = do 
  z <- [1..]
  x <- [1..z]
  y <- [x..z]
  guard (x^2 + y^2 == z^2)
  return (x, y, z)

pythags'' = 
  [1..]   >>= \z ->
  [1..z]  >>= \x ->
  [x..z]  >>= \y ->
  guard (x^2 + y^2 == z^2) >>= \_ ->
  return (x,y,z) 

