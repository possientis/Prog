import Test.HUnit
import FirstOrder
import Formula
import GFormula


newtype V = V Int deriving (Eq)

instance Show V where
  show (V 0) = "x"
  show (V 1) = "y"
  show (V 2) = "z"

x = V 0
y = V 1 

p1 = belong x y :: Formula V
p2 = bot        :: Formula V
p3 = imply p1 p2
p4 = forall x p1

q1 = belong x y :: GFormula V
q2 = bot        :: GFormula V
q3 = imply q1 q2
q4 = forall x q1

main = do
  putStrLn $ "p1 = " ++ (show p1)
  putStrLn $ "p2 = " ++ (show p2)
  putStrLn $ "p3 = " ++ (show p3)
  putStrLn $ "p4 = " ++ (show p4)
  putStrLn $ "q1 = " ++ (show q1)
  putStrLn $ "q2 = " ++ (show q2)
  putStrLn $ "q3 = " ++ (show q3)
  putStrLn $ "q4 = " ++ (show q4)

test1 = TestCase (assertEqual "(==).0" p2 p1)


