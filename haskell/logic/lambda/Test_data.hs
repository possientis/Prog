module Test_data
  ( p1, p2, p3, p4, p5, p6, p7, p8, p9
  , q1, q2, q3, q4, q5, q6, q7, q8
  , s1, s2, s3, s4, s5, s6, s7, s8
  , var1, var2, var3, var4, var5, var6, var7, var8
  , free1, free2, free3, free4, free5, free6, free7, free8
  , bnd1, bnd2, bnd3, bnd4, bnd5, bnd6, bnd7, bnd8
  , sub1, sub2, sub3, sub4, sub5, sub6, sub7, sub8
  , f1, f2, f3, f4
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

p9 = lambda x $ lambda y $ apply 
  (lambda z (apply (variable z) (variable x))) 
  (lambda x (apply (variable x) (variable y))) 


q1 = variable x'                :: Formula W
q2 = variable y'                :: Formula W
q3 = apply q1 q2
q4 = lambda x' q1
q5 = lambda x' (lambda y' q1)   :: Formula W
q6 = lambda x' (lambda y' q2)   :: Formula W
q7 = lambda x' (lambda y' q3) 
q8 = lambda x' (lambda y' (apply q1 q3))


var1 = singleton x    :: Set V
var2 = singleton y    :: Set V
var3 = fromList [x,y] :: Set V         
var4 = var1
var5 = var3
var6 = var3
var7 = var3
var8 = var7

free1 = var1
free2 = var2
free3 = var3
free4 = empty         :: Set V
free5 = free4
free6 = free4
free7 = free4
free8 = free4


bnd1  = empty           :: Set V
bnd2  = bnd1
bnd3  = bnd1
bnd4  = singleton x
bnd5  = fromList [x,y]
bnd6  = bnd5
bnd7  = bnd5
bnd8  = bnd5


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

f2 :: V -> W
f2 v  | v == x    = x'
      | v == y    = x'
      | v == z    = z'
      | otherwise = z'

f3 :: V -> W
f3 v  | v == x    = x'
      | v == y    = y'
      | v == z    = x'
      | otherwise = z'


f4 :: V -> W
f4 v  | v == x    = x'
      | v == y    = y'
      | v == z    = y'
      | otherwise = z'

