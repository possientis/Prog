module Test_isVal
  ( test_isVal
  ) where

import Term
import Test.HUnit

t1 = TmZero
t2 = TmSucc t1
t3 = TmSucc t2
t4 = TmSucc t3
t5 = TmSucc t4
t6 = TmTrue
t7 = TmFalse

f3 = TmIf TmTrue TmZero TmZero
f4 = TmIf TmFalse TmZero TmZero
f5 = TmSucc f3
f6 = TmSucc f4
f7 = TmPred(TmZero)
f8 = TmPred(TmSucc TmZero)
f9 = TmIsZero TmZero

test1 = TestCase $ assertBool "test1" $ isVal t1
test2 = TestCase $ assertBool "test2" $ isVal t2
test3 = TestCase $ assertBool "test3" $ isVal t3
test4 = TestCase $ assertBool "test4" $ isVal t4
test5 = TestCase $ assertBool "test5" $ isVal t5
test6 = TestCase $ assertBool "test6" $ isVal t6
test7 = TestCase $ assertBool "test7" $ isVal t7

test8 = TestCase $ assertBool "test8" $ not $ isVal f3
test9 = TestCase $ assertBool "test9" $ not $ isVal f4
test10= TestCase $ assertBool "test10"$ not $ isVal f5
test11= TestCase $ assertBool "test11"$ not $ isVal f6
test12= TestCase $ assertBool "test12"$ not $ isVal f7
test13= TestCase $ assertBool "test13"$ not $ isVal f8
test14= TestCase $ assertBool "test14"$ not $ isVal f9


test_isVal = TestLabel "isVal" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6
  , test7,  test8,  test9,  test10, test11, test12
  , test13, test14
  ]


