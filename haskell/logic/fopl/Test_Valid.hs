module Test_Valid
  ( test_Valid
  ) where

import Test.HUnit

import Test_data
import Valid

-- f1: V -> W is injective on (var pi) for all i=1,..,8
test1   = TestCase  $ assertBool "test1"  $ isValidFor f1 p1
test2   = TestCase  $ assertBool "test2"  $ isValidFor f1 p2
test3   = TestCase  $ assertBool "test3"  $ isValidFor f1 p3
test4   = TestCase  $ assertBool "test4"  $ isValidFor f1 p4
test5   = TestCase  $ assertBool "test5"  $ isValidFor f1 p5
test6   = TestCase  $ assertBool "test6"  $ isValidFor f1 p6
test7   = TestCase  $ assertBool "test7"  $ isValidFor f1 p7
test8   = TestCase  $ assertBool "test8"  $ isValidFor f1 p8

-- f2 x = f2 y, so f2 not valid for Ax.x:y
test9   = TestCase  $ assertBool "test9"  $ isValidFor f2 p1
test10  = TestCase  $ assertBool "test10" $ isValidFor f2 p2
test11  = TestCase  $ assertBool "test11" $ isValidFor f2 p3
test12  = TestCase  $ assertBool "test12" $ not $ isValidFor f2 p4
test13  = TestCase  $ assertBool "test13" $ isValidFor f2 p5
test14  = TestCase  $ assertBool "test14" $ isValidFor f2 p6
test15  = TestCase  $ assertBool "test15" $ isValidFor f2 p7
test16  = TestCase  $ assertBool "test16" $ isValidFor f2 p8

-- f3 z = f3 x, so f3 not valid for Az.(z:x -> z:y)
test17  = TestCase  $ assertBool "test17" $ isValidFor f3 p1
test18  = TestCase  $ assertBool "test18" $ isValidFor f3 p2
test19  = TestCase  $ assertBool "test19" $ isValidFor f3 p3
test20  = TestCase  $ assertBool "test20" $ isValidFor f3 p4
test21  = TestCase  $ assertBool "test21" $ isValidFor f3 p5
test22  = TestCase  $ assertBool "test22" $ isValidFor f3 p6
test23  = TestCase  $ assertBool "test23" $ isValidFor f3 p7
test24  = TestCase  $ assertBool "test24" $ not $ isValidFor f3 p8


test_Valid = TestLabel "test_valid" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  ]
