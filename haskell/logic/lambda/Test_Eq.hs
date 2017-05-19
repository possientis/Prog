module Test_Eq 
  ( test_Eq
  ) where

import Test.HUnit
import Test_data

test1   = TestCase $ assertEqual  "Eq.1"    p1 p1
test2   = TestCase $ assertEqual  "Eq.2"    p2 p2
test3   = TestCase $ assertEqual  "Eq.3"    p3 p3
test4   = TestCase $ assertEqual  "Eq.4"    p4 p4
test5   = TestCase $ assertBool   "Eq.5"    (p1 /= p2)
test6   = TestCase $ assertBool   "Eq.6"    (p2 /= p1)
test7   = TestCase $ assertBool   "Eq.7"    (p1 /= p3)
test8   = TestCase $ assertBool   "Eq.8"    (p3 /= p1)
test9   = TestCase $ assertBool   "Eq.9"    (p1 /= p4)
test10  = TestCase $ assertBool   "Eq.10"   (p4 /= p1)
test11  = TestCase $ assertBool   "Eq.11"   (p2 /= p3)
test12  = TestCase $ assertBool   "Eq.12"   (p3 /= p2)

test_Eq = TestLabel "test_Eq" $ TestList
  [ test1,    test2,    test3,    test4,    test5
  , test6,    test7,    test8,    test9,    test10
  , test11,   test12
  ]


