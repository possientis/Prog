module Test_data
  ( p1,   p2,   p3,   p4,   p5,   p6,   p7,   p8,   p9
  , q1,   q2,   q3,   q4,   q5,   q6,   q7,   q8
  , s1,   s2,   s3,   s4,   s5,   s6,   s7,   s8,   s9
  , s1',  s2',  s3',  s4',  s5',  s6',  s7',  s8',  s9'
  , t1,   t2,   t3,   t4,   t5,   t6,   t7,   t8,   t9
  , var1, var2, var3, var4, var5, var6, var7, var8
  , free1, free2, free3, free4, free5, free6, free7, free8
  , bnd1, bnd2, bnd3, bnd4, bnd5, bnd6, bnd7, bnd8
  , sub1, sub2, sub3 , sub4, sub5, sub6, sub7, sub8
  , f1, f2, f3, f4
  , x, y, z
  , x', y', z'
  ) where

import Data.Set

import Formula            -- main implementation
import V
import Bar

s1 = "x:y"
s2 = "!"
s3 = "(x:y -> !)"
s4 = "Ax.x:y"
s5 = "z:x"
s6 = "z:y"
s7 = "(z:x -> z:y)"
s8 = "Az.(z:x -> z:y)"
s9 = "Ax.Ay.(Az.z:x -> Ax.x:y)"

-- minimal transform representations
s1'= s1
s2'= s2
s3'= s3
s4'= "A0.0:y"
s5'= s5
s6'= s6
s7'= s7
s8'= "A0.(0:x -> 0:y)"
s9'= "A2.A1.(A0.0:2 -> A0.0:1)"

p1 = belong x y   :: Formula V
p2 = bot          :: Formula V
p3 = imply p1 p2
p4 = forAll x p1
p5 = belong z x   :: Formula V
p6 = belong z y   :: Formula V
p7 = imply p5 p6
p8 = forAll z p7

p9 = forAll x $ forAll y $ imply 
  (forAll z (belong z x)) 
  (forAll x (belong x y))

q1 = belong x' y' :: Formula W
q2 = bot          :: Formula W
q3 = imply q1 q2
q4 = forAll x' q1
q5 = belong z' x' :: Formula W
q6 = belong z' y' :: Formula W
q7 = imply q5 q6
q8 = forAll z' q7

t1 = belong (left x) (left y) :: Formula (Bar V)
t2 = bot                      :: Formula (Bar V)
t3 = imply t1 t2
t4 = forAll (right 0) $ belong (right 0) (left y)
t5 = belong (left z) (left x)
t6 = belong (left z) (left y)
t7 = imply t5 t6
t8 = forAll (right 0) $ imply 
  (belong (right 0) (left x)) 
  (belong (right 0) (left y))  

t9 = forAll (right 2) $ forAll (right 1) $ imply
  (forAll (right 0) $ belong (right 0) (right 2))
  (forAll (right 0) $ belong (right 0) (right 1)) :: Formula (Bar V)


var1 = fromList [x,y]   :: Set V
var2 = empty            :: Set V
var3 = var1         
var4 = var1
var5 = fromList [x,z]   :: Set V 
var6 = fromList [y,z]   :: Set V 
var7 = fromList [x,y,z] :: Set V 
var8 = var7

free1 = var1
free2 = var2
free3 = free1
free4 = singleton y
free5 = var5
free6 = var6
free7 = var7
free8 = var1

bnd1  = empty           :: Set V
bnd2  = bnd1
bnd3  = bnd1
bnd4  = singleton x
bnd5  = bnd1
bnd6  = bnd1
bnd7  = bnd1
bnd8  = singleton z


sub1 = singleton p1   :: Set (Formula V)
sub2 = singleton p2   :: Set (Formula V)
sub3 = fromList [ p3, p1, p2 ]
sub4 = fromList [ p4, p1]
sub5 = singleton p5
sub6 = singleton p6
sub7 = fromList [ p7, p5, p6 ]
sub8 = fromList [ p8, p7, p5, p6 ]



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

