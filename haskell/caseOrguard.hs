sign :: Int -> Int
sign n
  | n < 0     = (-1)
  | n == 0    =   0
  | n > 0     =   1 
  | otherwise =   5 -- unlikely

data Roll = One | Two | Three | Four | Five | Six

value :: Roll -> Int
value x = case x of
  One   -> 1
  Two   -> 2
  Three -> 3
  Four  -> 4
  Five  -> 5
  Six   -> 6 

value' :: Roll -> Int
value' One    = 1
value' Two    = 2
value' Three  = 3
value' Four   = 4
value' Five   = 5
value' Six    = 6
