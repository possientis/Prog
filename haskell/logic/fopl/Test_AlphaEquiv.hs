module Test_AlphaEquiv
  ( test_AlphaEquiv
  ) where

import Test.HUnit

import Test_data
import AlphaEquiv
import Formula
import V

test1   = TestCase  $ assertBool "test1"  $ alphaEq p1 p1
test2   = TestCase  $ assertBool "test2"  $ alphaEq p2 p2
test3   = TestCase  $ assertBool "test3"  $ alphaEq p3 p3
test4   = TestCase  $ assertBool "test4"  $ alphaEq p4 p4
test5   = TestCase  $ assertBool "test5"  $ alphaEq p5 p5
test6   = TestCase  $ assertBool "test6"  $ alphaEq p6 p6
test7   = TestCase  $ assertBool "test7"  $ alphaEq p7 p7
test8   = TestCase  $ assertBool "test8"  $ alphaEq p8 p8


test9   = TestCase  $ assertBool "test9"  $ not $ alphaEq p1 $ belong x x
test10  = TestCase  $ assertBool "test10" $ not $ alphaEq p1 $ belong y x
test11  = TestCase  $ assertBool "test11" $ not $ alphaEq p1 $ belong z x
test12  = TestCase  $ assertBool "test12" $       alphaEq p1 $ belong x y
test13  = TestCase  $ assertBool "test13" $ not $ alphaEq p1 $ belong y y
test14  = TestCase  $ assertBool "test14" $ not $ alphaEq p1 $ belong z y
test15  = TestCase  $ assertBool "test15" $ not $ alphaEq p1 $ belong x z
test16  = TestCase  $ assertBool "test16" $ not $ alphaEq p1 $ belong y z


test_AlphaEquiv = TestLabel "test_valid" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  ]

