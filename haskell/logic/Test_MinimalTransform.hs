module Test_MinimalTransform
  ( test_MinimalTransform
  ) where

import Data.Functor ((<$>))
import Prelude hiding (filter)
import Test.HUnit
import Data.Set

import Test_data
import MinimalTransform
import Bar
import Variable
import AlphaEquiv



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

-- Bnd (M p) = Var (M p) /\ N
keepInt :: Set (Bar v) -> Set (Bar v)
keepInt = filter isInt 
test17  = TestCase  $ assertEqual "test17"  (bound t1) $ keepInt (var t1)
test18  = TestCase  $ assertEqual "test18"  (bound t9) $ keepInt (var t9)
test19  = TestCase  $ assertEqual "test19"  (bound t3) $ keepInt (var t3)
test20  = TestCase  $ assertEqual "test20"  (bound t4) $ keepInt (var t4)
test21  = TestCase  $ assertEqual "test21"  (bound t5) $ keepInt (var t5)
test22  = TestCase  $ assertEqual "test22"  (bound t6) $ keepInt (var t6)
test23  = TestCase  $ assertEqual "test23"  (bound t7) $ keepInt (var t7)
test24  = TestCase  $ assertEqual "test24"  (bound t8) $ keepInt (var t8)

-- M p ~ i p where i: V -> Bar V inclusion map
test25  = TestCase  $ assertBool "test25"  $  alphaEq t1 (left <$> p1)
test26  = TestCase  $ assertBool "test26"  $  alphaEq t9 (left <$> p9)
test27  = TestCase  $ assertBool "test27"  $  alphaEq t3 (left <$> p3)
test28  = TestCase  $ assertBool "test28"  $  alphaEq t4 (left <$> p4)
test29  = TestCase  $ assertBool "test29"  $  alphaEq t5 (left <$> p5)
test30  = TestCase  $ assertBool "test30"  $  alphaEq t6 (left <$> p6)
test31  = TestCase  $ assertBool "test31"  $  alphaEq t7 (left <$> p7)
test32  = TestCase  $ assertBool "test32"  $  alphaEq t8 (left <$> p8)

-- Fr (M p) = Var (M p) /\ V
keepV :: Set (Bar v) -> Set (Bar v)
keepV = filter isV
test33  = TestCase  $ assertEqual "test33"  (free t1) $ keepV (var t1)
test34  = TestCase  $ assertEqual "test34"  (free t9) $ keepV (var t9)
test35  = TestCase  $ assertEqual "test35"  (free t3) $ keepV (var t3)
test36  = TestCase  $ assertEqual "test36"  (free t4) $ keepV (var t4)
test37  = TestCase  $ assertEqual "test37"  (free t5) $ keepV (var t5)
test38  = TestCase  $ assertEqual "test38"  (free t6) $ keepV (var t6)
test39  = TestCase  $ assertEqual "test39"  (free t7) $ keepV (var t7)
test40  = TestCase  $ assertEqual "test40"  (free t8) $ keepV (var t8)



test_MinimalTransform = TestLabel "test_minimalTransform" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24 
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  ]

