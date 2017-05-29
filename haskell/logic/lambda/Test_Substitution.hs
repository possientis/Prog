module Test_Substitution
  ( test_Substitution
  ) where

import Test.HUnit

import Test_data
import Substitution


test1   = TestCase $ assertEqual "test1"  ((x <-: x) x) x 
test2   = TestCase $ assertEqual "test2"  ((x <-: x) y) y 
test3   = TestCase $ assertEqual "test3"  ((x <-: x) z) z 
test4   = TestCase $ assertEqual "test4"  ((x <-: y) x) x 
test5   = TestCase $ assertEqual "test5"  ((x <-: y) y) x 
test6   = TestCase $ assertEqual "test6"  ((x <-: y) z) z 
test7   = TestCase $ assertEqual "test7"  ((x <-: z) x) x 
test8   = TestCase $ assertEqual "test8"  ((x <-: z) y) y 
test9   = TestCase $ assertEqual "test9"  ((x <-: z) z) x 
test10  = TestCase $ assertEqual "test10" ((y <-: x) x) y 
test11  = TestCase $ assertEqual "test11" ((y <-: x) y) y 
test12  = TestCase $ assertEqual "test12" ((y <-: x) z) z 
test13  = TestCase $ assertEqual "test13" ((y <-: y) x) x 
test14  = TestCase $ assertEqual "test14" ((y <-: y) y) y 
test15  = TestCase $ assertEqual "test15" ((y <-: y) z) z 
test16  = TestCase $ assertEqual "test16" ((y <-: z) x) x 
test17  = TestCase $ assertEqual "test17" ((y <-: z) y) y 
test18  = TestCase $ assertEqual "test18" ((y <-: z) z) y 
test19  = TestCase $ assertEqual "test19" ((z <-: x) x) z 
test20  = TestCase $ assertEqual "test20" ((z <-: x) y) y 
test21  = TestCase $ assertEqual "test21" ((z <-: x) z) z 
test22  = TestCase $ assertEqual "test22" ((z <-: y) x) x 
test23  = TestCase $ assertEqual "test23" ((z <-: y) y) z 
test24  = TestCase $ assertEqual "test24" ((z <-: y) z) z 
test25  = TestCase $ assertEqual "test25" ((z <-: z) x) x 
test26  = TestCase $ assertEqual "test26" ((z <-: z) y) y 
test27  = TestCase $ assertEqual "test27" ((z <-: z) z) z 

test28   = TestCase $ assertEqual "test28"  ((x <-> x) x) x 
test29   = TestCase $ assertEqual "test29"  ((x <-> x) y) y 
test30   = TestCase $ assertEqual "test30"  ((x <-> x) z) z 
test31   = TestCase $ assertEqual "test31"  ((x <-> y) x) y 
test32   = TestCase $ assertEqual "test32"  ((x <-> y) y) x 
test33   = TestCase $ assertEqual "test33"  ((x <-> y) z) z 
test34   = TestCase $ assertEqual "test34"  ((x <-> z) x) z
test35   = TestCase $ assertEqual "test35"  ((x <-> z) y) y 
test36   = TestCase $ assertEqual "test36"  ((x <-> z) z) x 
test37   = TestCase $ assertEqual "test37"  ((y <-> x) x) y 
test38   = TestCase $ assertEqual "test38"  ((y <-> x) y) x 
test39   = TestCase $ assertEqual "test39"  ((y <-> x) z) z 
test40   = TestCase $ assertEqual "test40"  ((y <-> y) x) x 
test41   = TestCase $ assertEqual "test41"  ((y <-> y) y) y 
test42   = TestCase $ assertEqual "test42"  ((y <-> y) z) z 
test43   = TestCase $ assertEqual "test43"  ((y <-> z) x) x
test44   = TestCase $ assertEqual "test44"  ((y <-> z) y) z 
test45   = TestCase $ assertEqual "test45"  ((y <-> z) z) y 
test46   = TestCase $ assertEqual "test46"  ((z <-> x) x) z 
test47   = TestCase $ assertEqual "test47"  ((z <-> x) y) y 
test48   = TestCase $ assertEqual "test48"  ((z <-> x) z) x 
test49   = TestCase $ assertEqual "test49"  ((z <-> y) x) x 
test50   = TestCase $ assertEqual "test50"  ((z <-> y) y) z 
test51   = TestCase $ assertEqual "test51"  ((z <-> y) z) y 
test52   = TestCase $ assertEqual "test52"  ((z <-> z) x) x
test53   = TestCase $ assertEqual "test53"  ((z <-> z) y) y 
test54   = TestCase $ assertEqual "test54"  ((z <-> z) z) z 







test_Substitution = TestLabel "test_substitution" $ TestList 
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8,  test9
  , test10, test11, test12, test13, test14, test15, test16, test17, test18
  , test19, test20, test21, test22, test23, test24, test25, test26, test27
  , test28, test29, test30, test31, test32, test33, test34, test35, test36
  , test37, test38, test39, test40, test41, test42, test43, test44, test45
  , test46, test47, test48, test49, test50, test51, test52, test53, test54
  ]


