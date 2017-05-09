module Test_isNumerical
  ( test_isNumerical
  ) where

import Term
import Test.HUnit

t1 = TmZero
t2 = TmSucc t1
t3 = TmSucc t2
t4 = TmSucc t3
t5 = TmSucc t4

f1 = TmTrue
f2 = TmFalse
f3 = TmIf TmTrue TmZero TmZero
f4 = TmIf TmFalse TmZero TmZero
f5 = TmSucc f3
f6 = TmSucc f4
f7 = TmPred(TmZero)
f8 = TmPred(TmSucc TmZero)
f9 = TmIsZero TmZero

test1 = TestCase $ assertBool "test1" $ isNumerical t1
test2 = TestCase $ assertBool "test2" $ isNumerical t2
test3 = TestCase $ assertBool "test3" $ isNumerical t3
test4 = TestCase $ assertBool "test4" $ isNumerical t4
test5 = TestCase $ assertBool "test5" $ isNumerical t5

test6 = TestCase $ assertBool "test6" $ not $ isNumerical f1
test7 = TestCase $ assertBool "test7" $ not $ isNumerical f2
test8 = TestCase $ assertBool "test8" $ not $ isNumerical f3
test9 = TestCase $ assertBool "test9" $ not $ isNumerical f4
test10= TestCase $ assertBool "test10"$ not $ isNumerical f5
test11= TestCase $ assertBool "test11"$ not $ isNumerical f6
test12= TestCase $ assertBool "test12"$ not $ isNumerical f7
test13= TestCase $ assertBool "test13"$ not $ isNumerical f8
test14= TestCase $ assertBool "test14"$ not $ isNumerical f9


test_isNumerical = TestLabel "isNumerical" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6
  , test7,  test8,  test9,  test10, test11, test12
  , test13, test14
  ]


