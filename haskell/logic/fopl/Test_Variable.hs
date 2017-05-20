module Test_Variable
  ( test_Variable
  ) where

import Test.HUnit
import Data.Set

import Test_data
import Variable

test1 = TestCase $ assertEqual "test1" (var p1) v1 
test2 = TestCase $ assertEqual "test2" (var p2) v2
test3 = TestCase $ assertEqual "test3" (var p3) v3
test4 = TestCase $ assertEqual "test4" (var p4) v4
test5 = TestCase $ assertEqual "test5" (var p5) v5
test6 = TestCase $ assertEqual "test6" (var p6) v6
test7 = TestCase $ assertEqual "test7" (var p7) v7
test8 = TestCase $ assertEqual "test8" (var p8) v8


test_Variable = TestLabel "test_var" $ TestList 
  [ test1,  test2,  test3,  test4, test5, test6, test7, test8
  ]
