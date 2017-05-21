module Test_SubFormula
  ( test_SubFormula
  ) where

import Test.HUnit
import Test_data
import SubFormula

test1   = TestCase $ assertEqual "sub.1" (sub p1) sub1
test2   = TestCase $ assertEqual "sub.2" (sub p2) sub2
test3   = TestCase $ assertEqual "sub.3" (sub p3) sub3
test4   = TestCase $ assertEqual "sub.4" (sub p4) sub4
test5   = TestCase $ assertEqual "sub.5" (sub p5) sub5
test6   = TestCase $ assertEqual "sub.6" (sub p6) sub6
test7   = TestCase $ assertEqual "sub.7" (sub p7) sub7
test8   = TestCase $ assertEqual "sub.8" (sub p8) sub8

test9   = TestCase $ assertBool  "sub.9"  $ p1 <=: p1
test10  = TestCase $ assertBool  "sub.10" $ not $ p1 <=: p2
test11  = TestCase $ assertBool  "sub.11" $ p1 <=: p3
test12  = TestCase $ assertBool  "sub.12" $ p1 <=: p4
test13  = TestCase $ assertBool  "sub.13" $ not $ p1 <=: p5
test14  = TestCase $ assertBool  "sub.14" $ not $ p1 <=: p6
test15  = TestCase $ assertBool  "sub.15" $ not $ p1 <=: p7
test16  = TestCase $ assertBool  "sub.16" $ not $ p1 <=: p8

test17  = TestCase $ assertBool  "sub.17" $ not $ p2 <=: p1
test18  = TestCase $ assertBool  "sub.18" $ p2 <=: p2
test19  = TestCase $ assertBool  "sub.19" $ p2 <=: p3
test20  = TestCase $ assertBool  "sub.20" $ not $ p2 <=: p4
test21  = TestCase $ assertBool  "sub.21" $ not $ p2 <=: p5
test22  = TestCase $ assertBool  "sub.22" $ not $ p2 <=: p6
test23  = TestCase $ assertBool  "sub.23" $ not $ p2 <=: p7
test24  = TestCase $ assertBool  "sub.24" $ not $ p2 <=: p8


test_SubFormula = TestLabel "test_SubFormula" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  ]
