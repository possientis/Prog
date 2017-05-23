module Test_data
  ( p1, p2, p3, p4, p5, p6, p7, p8
  , q1, q2, q3, q4, q5, q6, q7, q8
  , s1, s2, s3, s4, s5, s6, s7, s8
  , v1, v2, v3, v4, v5, v6, v7, v8
  , sub1, sub2, sub3 , sub4, sub5, sub6, sub7, sub8
  , f1
  , x, y, z
  , x', y', z'
  ) where

import Data.Set

import Formula               -- main implementation
import V

s1 = "x"
s2 = "y"
s3 = "(x y)"
s4 = "Lx.x"
s5 = "Lx.Ly.x"
s6 = "Lx.Ly.y"
s7 = "Lx.Ly.(x y)"
s8 = "Lx.Ly.(x (x y))"

p1 = variable x                 :: Formula V
p2 = variable y                 :: Formula V
p3 = apply p1 p2
p4 = lambda x p1
p5 = lambda x (lambda y p1)     :: Formula V
p6 = lambda x (lambda y p2)     :: Formula V
p7 = lambda x (lambda y p3) 
p8 = lambda x (lambda y (apply p1 p3))

q1 = variable x'                :: Formula W
q2 = variable y'                :: Formula W
q3 = apply q1 q2
q4 = lambda x' q1
q5 = lambda x' (lambda y' q1)   :: Formula W
q6 = lambda x' (lambda y' q2)   :: Formula W
q7 = lambda x' (lambda y' q3) 
q8 = lambda x' (lambda y' (apply q1 q3))


v1 = fromList [x]   :: Set V
v2 = fromList [y]   :: Set V
v3 = fromList [x,y] :: Set V         
v4 = v1
v5 = v3
v6 = v3
v7 = v3
v8 = v7

sub1 = singleton p1   :: Set (Formula V)
sub2 = singleton p2   :: Set (Formula V)
sub3 = fromList [ p3, p1, p2 ]
sub4 = fromList [ p4, p1]
sub5 = fromList [ p5, lambda y p1, p1 ] 
sub6 = fromList [ p6, lambda y p2, p2 ]
sub7 = fromList [ p7, lambda y p3, p3, p1, p2 ]
sub8 = fromList [ p8, lambda y (apply p1 p3), apply p1 p3, p1, p3, p2 ] 

f1 :: V -> W
f1 v  | v == x    = x'
      | v == y    = y'
      | v == z    = z'
      | otherwise = z'


