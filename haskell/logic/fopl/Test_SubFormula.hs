module Test_SubFormula
  ( test_SubFormula
  ) where

import Test.HUnit
import Data.Set
import Prelude hiding (map) -- conflict with Data.Set
import Test_data
import SubFormula
import Variable


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

test25  = TestCase $ assertBool  "sub.25" $ not $ p3 <=: p1
test26  = TestCase $ assertBool  "sub.26" $ not $ p3 <=: p2
test27  = TestCase $ assertBool  "sub.27" $ p3 <=: p3
test28  = TestCase $ assertBool  "sub.28" $ not $ p3 <=: p4
test29  = TestCase $ assertBool  "sub.29" $ not $ p3 <=: p5
test30  = TestCase $ assertBool  "sub.30" $ not $ p3 <=: p6
test31  = TestCase $ assertBool  "sub.31" $ not $ p3 <=: p7
test32  = TestCase $ assertBool  "sub.32" $ not $ p3 <=: p8

test33  = TestCase $ assertBool  "sub.33" $ not $ p4 <=: p1
test34  = TestCase $ assertBool  "sub.34" $ not $ p4 <=: p2
test35  = TestCase $ assertBool  "sub.35" $ not $ p4 <=: p3
test36  = TestCase $ assertBool  "sub.36" $ p4 <=: p4
test37  = TestCase $ assertBool  "sub.37" $ not $ p4 <=: p5
test38  = TestCase $ assertBool  "sub.38" $ not $ p4 <=: p6
test39  = TestCase $ assertBool  "sub.39" $ not $ p4 <=: p7
test40  = TestCase $ assertBool  "sub.40" $ not $ p4 <=: p8

test41  = TestCase $ assertBool  "sub.41" $ not $ p5 <=: p1
test42  = TestCase $ assertBool  "sub.42" $ not $ p5 <=: p2
test43  = TestCase $ assertBool  "sub.43" $ not $ p5 <=: p3
test44  = TestCase $ assertBool  "sub.44" $ not $ p5 <=: p4
test45  = TestCase $ assertBool  "sub.45" $ p5 <=: p5
test46  = TestCase $ assertBool  "sub.46" $ not $ p5 <=: p6
test47  = TestCase $ assertBool  "sub.47" $ p5 <=: p7
test48  = TestCase $ assertBool  "sub.48" $ p5 <=: p8

test49  = TestCase $ assertBool  "sub.49" $ not $ p6 <=: p1
test50  = TestCase $ assertBool  "sub.50" $ not $ p6 <=: p2
test51  = TestCase $ assertBool  "sub.51" $ not $ p6 <=: p3
test52  = TestCase $ assertBool  "sub.52" $ not $ p6 <=: p4
test53  = TestCase $ assertBool  "sub.53" $ not $ p6 <=: p5
test54  = TestCase $ assertBool  "sub.54" $ p6 <=: p6
test55  = TestCase $ assertBool  "sub.55" $ p6 <=: p7
test56  = TestCase $ assertBool  "sub.56" $ p6 <=: p8

test57  = TestCase $ assertBool  "sub.57" $ not $ p7 <=: p1
test58  = TestCase $ assertBool  "sub.58" $ not $ p7 <=: p2
test59  = TestCase $ assertBool  "sub.59" $ not $ p7 <=: p3
test60  = TestCase $ assertBool  "sub.60" $ not $ p7 <=: p4
test61  = TestCase $ assertBool  "sub.61" $ not $ p7 <=: p5
test62  = TestCase $ assertBool  "sub.62" $ not $ p7 <=: p6
test63  = TestCase $ assertBool  "sub.63" $ p7 <=: p7
test64  = TestCase $ assertBool  "sub.64" $ p7 <=: p8

test65  = TestCase $ assertBool  "sub.65" $ not $ p8 <=: p1
test66  = TestCase $ assertBool  "sub.66" $ not $ p8 <=: p2
test67  = TestCase $ assertBool  "sub.67" $ not $ p8 <=: p3
test68  = TestCase $ assertBool  "sub.68" $ not $ p8 <=: p4
test69  = TestCase $ assertBool  "sub.69" $ not $ p8 <=: p5
test70  = TestCase $ assertBool  "sub.70" $ not $ p8 <=: p6
test71  = TestCase $ assertBool  "sub.71" $ not $ p8 <=: p7
test72  = TestCase $ assertBool  "sub.72" $ p8 <=: p8

-- if p is a subformula of q, then the variables of p are a subset of those of q
-- p <=: q -> var p <= var q
test73  = TestCase $ assertBool  "sub.73" $ isSubsetOf (var p1) (var p3)
test74  = TestCase $ assertBool  "sub.74" $ isSubsetOf (var p1) (var p4)
test75  = TestCase $ assertBool  "sub.75" $ isSubsetOf (var p2) (var p3)
test76  = TestCase $ assertBool  "sub.76" $ isSubsetOf (var p5) (var p7)
test77  = TestCase $ assertBool  "sub.77" $ isSubsetOf (var p5) (var p8)
test78  = TestCase $ assertBool  "sub.78" $ isSubsetOf (var p6) (var p7)
test79  = TestCase $ assertBool  "sub.79" $ isSubsetOf (var p6) (var p8)
test80  = TestCase $ assertBool  "sub.80" $ isSubsetOf (var p7) (var p8)
test81  = TestCase $ assertBool  "sub.81" $ isSubsetOf (var p7) (var p8) -- dummy
test82  = TestCase $ assertBool  "sub.82" $ isSubsetOf (var p7) (var p8) -- dummy
test83  = TestCase $ assertBool  "sub.83" $ isSubsetOf (var p7) (var p8) -- dummy

-- the subformulas of (f p) is the direct image by f of the subformulas of p
-- sub (f p) = f[sub p] 
test84  = TestCase $ assertEqual  "sub.84" (sub (f1<$>p1)) $ map (f1<$>) (sub p1)
test85  = TestCase $ assertEqual  "sub.85" (sub (f1<$>p2)) $ map (f1<$>) (sub p2)
test86  = TestCase $ assertEqual  "sub.86" (sub (f1<$>p3)) $ map (f1<$>) (sub p3)
test87  = TestCase $ assertEqual  "sub.87" (sub (f1<$>p4)) $ map (f1<$>) (sub p4)
test88  = TestCase $ assertEqual  "sub.88" (sub (f1<$>p5)) $ map (f1<$>) (sub p5)
test89  = TestCase $ assertEqual  "sub.89" (sub (f1<$>p6)) $ map (f1<$>) (sub p6)
test90  = TestCase $ assertEqual  "sub.90" (sub (f1<$>p7)) $ map (f1<$>) (sub p7)
test91  = TestCase $ assertEqual  "sub.91" (sub (f1<$>p8)) $ map (f1<$>) (sub p8)

test_SubFormula = TestLabel "test_SubFormula" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  , test41, test42, test43, test44, test45, test46, test47, test48
  , test49, test50, test51, test52, test53, test54, test55, test56
  , test57, test58, test59, test60, test61, test62, test63, test64
  , test65, test66, test67, test68, test69, test70, test71, test72
  , test73, test74, test75, test76, test77, test78, test79, test80
  , test81, test82, test83, test84, test85, test86, test87, test88
  , test89, test90, test91
  ]



