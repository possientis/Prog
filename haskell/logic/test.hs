import FirstOrder
import Formula
import GFormula


type V = Int

x = 0 :: V
y = 1 :: V 

p1 = belong x y :: Formula V
p2 = bot        :: Formula V
p3 = imply p1 p2
p4 = forall x p1

q1 = belong x y :: GFormula V
q2 = bot        :: GFormula V
q3 = imply q1 q2
q4 = forall x q1



