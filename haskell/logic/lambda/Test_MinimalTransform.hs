module Test_MinimalTransform
  ( test_MinimalTransform
  ) where

import Test.HUnit

import Test_data
import MinimalTransform



test1   = TestCase  $ assertEqual "test1" t1 $ minTrans p1
test2   = TestCase  $ assertEqual "test2" t2 $ minTrans p2
test3   = TestCase  $ assertEqual "test3" t3 $ minTrans p3
test4   = TestCase  $ assertEqual "test4" t4 $ minTrans p4
test5   = TestCase  $ assertEqual "test5" t5 $ minTrans p5
test6   = TestCase  $ assertEqual "test6" t6 $ minTrans p6
test7   = TestCase  $ assertEqual "test7" t7 $ minTrans p7
test8   = TestCase  $ assertEqual "test8" t8 $ minTrans p8

test9   = TestCase  $ assertEqual "test9"   t9  $ minTrans p9
test10  = TestCase  $ assertEqual "test10"  s9  $ show p9
test11  = TestCase  $ assertEqual "test11"  s9' $ show $ minTrans p9

test12  = TestCase  $ assertEqual "test12"  s1' $ show $ minTrans p1
test13  = TestCase  $ assertEqual "test13"  s2' $ show $ minTrans p2
test14  = TestCase  $ assertEqual "test14"  s4' $ show $ minTrans p4
test15  = TestCase  $ assertEqual "test15"  s7' $ show $ minTrans p7
test16  = TestCase  $ assertEqual "test16"  s8' $ show $ minTrans p8



test_MinimalTransform = TestLabel "test_minimalTransform" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9, test10, test11,  test12, test13, test14, test15, test16
  ]

