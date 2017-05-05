{-# LANGUAGE AllowAmbiguousTypes #-}

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
z = V 2

runTest :: (FirstOrder m) => m V -> Test
runTest = undefined

p1 = belong x y :: Formula V
p2 = bot        :: Formula V
p3 = imply p1 p2
p4 = forall x p1

q1 = belong x y :: GFormula V
q2 = bot        :: GFormula V
q3 = imply q1 q2
q4 = forall x q1

test_equal r1 r2 r3 r4 = TestList 
  [ TestCase (assertEqual "x:y == x:y" r1 r1)

  ]

tests = TestList 
  [ TestLabel "Formula V: (==)"   $ test_equal p1 p2 p3 p4
  , TestLabel "GFormula V: (==)"  $ test_equal q1 q2 q3 q4
  ]
 

main = do
  runTestTT tests



