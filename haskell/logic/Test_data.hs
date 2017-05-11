module Test_data
  ( p1
  , p2
  , p3
  , p4
  , f1
  ) where

import V
import Formula
import FirstOrder

type TFormula = Formula    -- choose implementation

p1 = belong x y :: TFormula V
p2 = bot        :: TFormula V
p3 = imply p1 p2
p4 = forall x p1

f1 :: V -> Int
f1 v  | v == x    = 0
      | v == y    = 1
      | v == z    = 2
      | otherwise = 3


