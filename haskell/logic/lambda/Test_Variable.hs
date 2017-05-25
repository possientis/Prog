module Test_Variable
  ( test_Variable
  ) where

import Test.HUnit
import Data.Set

import Test_data
import Variable
import Prelude hiding (map) -- conflicts with Data.Set

test1 = TestCase $ assertEqual "test1" (var p1) v1 
test2 = TestCase $ assertEqual "test2" (var p2) v2
test3 = TestCase $ assertEqual "test3" (var p3) v3
test4 = TestCase $ assertEqual "test4" (var p4) v4
test5 = TestCase $ assertEqual "test5" (var p5) v5
test6 = TestCase $ assertEqual "test6" (var p6) v6
test7 = TestCase $ assertEqual "test7" (var p7) v7
test8 = TestCase $ assertEqual "test8" (var p8) v8

-- var (f p) = f[var p] (direct image) 
test9   = TestCase $ assertEqual "test9"  (var $ f1 <$> p1) (map f1 v1) 
test10  = TestCase $ assertEqual "test10" (var $ f1 <$> p2) (map f1 v2) 
test11  = TestCase $ assertEqual "test11" (var $ f1 <$> p3) (map f1 v3) 
test12  = TestCase $ assertEqual "test12" (var $ f1 <$> p4) (map f1 v4) 
test13  = TestCase $ assertEqual "test13" (var $ f1 <$> p5) (map f1 v5) 
test14  = TestCase $ assertEqual "test14" (var $ f1 <$> p6) (map f1 v6) 
test15  = TestCase $ assertEqual "test15" (var $ f1 <$> p7) (map f1 v7) 
test16  = TestCase $ assertEqual "test16" (var $ f1 <$> p8) (map f1 v8) 


test_Variable = TestLabel "test_var" $ TestList 
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  ]
