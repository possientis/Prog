module Test_data
  ( p1, p2, p3, p4, p5, p6, p7, p8
  , q1, q2, q3, q4, q5, q6, q7, q8
  , s1, s2, s3, s4, s5, s6, s7, s8
  , v1, v2, v3, v4, v5, v6, v7, v8
  , f1
  , x, y, z
  , x', y', z'
  ) where

import Data.Set

import Formula            -- main implementation
import V

s1 = "x:y"
s2 = "!"
s3 = "(x:y -> !)"
s4 = "Ax.x:y"
s5 = "z:x"
s6 = "z:y"
s7 = "(z:x -> z:y)"
s8 = "Az.(z:x -> z:y)"

p1 = belong x y   :: Formula V
p2 = bot          :: Formula V
p3 = imply p1 p2
p4 = forall x p1
p5 = belong z x   :: Formula V
p6 = belong z y   :: Formula V
p7 = imply p5 p6
p8 = forall z p7

q1 = belong x' y' :: Formula W
q2 = bot          :: Formula W
q3 = imply q1 q2
q4 = forall x' q1
q5 = belong z' x' :: Formula W
q6 = belong z' y' :: Formula W
q7 = imply q5 q6
q8 = forall z' q7

v1 = fromList [x,y]   :: Set V
v2 = empty            :: Set V
v3 = v1         
v4 = v1
v5 = fromList [x,z]   :: Set V 
v6 = fromList [y,z]   :: Set V 
v7 = fromList [x,y,z] :: Set V 
v8 = v7



f1 :: V -> W
f1 v  | v == x    = x'
      | v == y    = y'
      | v == z    = z'
      | otherwise = z'


