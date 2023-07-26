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

my_guard :: Bool -> [()]
my_guard True = [()]
my_guard False = []   -- mzero

my_bind :: [a] -> (a -> [b]) -> [b]
my_bind xs f = concatMap f xs

my_return :: a -> [a]
my_return x = [x]

val1 = [()] `my_bind` \_  -> return 10   -- [10]
val2 = []   `my_bind` \ _ -> return 10   -- []

{-
pythags2 =  concatMap f1 [1..]
  where f1 = \z -> concatMap f2 [1..z]
          where f2 = \x ->concatMap f3 [x..z]
                  where f3 = \y -> concatMap f4 $ guard (x^2 + y^2 == z^2)
                          where f4 = \_ -> return (x,y,z)
-}

pythags3 :: [(Int,Int,Int)]
pythags3 =
  let f4 z x y = \_ -> return (x, y, z)
      f3 z x   = \y -> concatMap (f4 z x y) (guard (x^2 + y^2 == z^2) :: [()])
      f2 z     = \x -> concatMap (f3 z x) [x..z]
      f1       = \z -> concatMap (f2 z) [1..z]
      in concatMap f1 [1..]

pythags4 :: [(Int,Int,Int)]
pythags4 =
  let ret x y z = [(x,y,z)]
      gd  z x y = concatMap (\_ -> ret x y z) (guard (x^2 + y^2 == z^2) :: [()])
      doY z x   = concatMap (gd z x)  [x..z]
      doX z     = concatMap (doY z)   [1..z]
      doZ       = concatMap (doX)     [1..]
  in doZ







