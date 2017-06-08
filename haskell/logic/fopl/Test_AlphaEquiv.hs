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

test17  = TestCase  $ assertBool "test17" $ not $ alphaEq p2 $ belong x y
test18  = TestCase  $ assertBool "test18" $       alphaEq p2 $ bot
test19  = TestCase  $ assertBool "test19" $ not $ alphaEq p2 $ imply bot bot 
test20  = TestCase  $ assertBool "test20" $ not $ alphaEq p2 $ forall x bot
test21  = TestCase  $ assertBool "test21" $ not $ alphaEq p2 $ p3 
test22  = TestCase  $ assertBool "test22" $ not $ alphaEq p2 $ p4
test23  = TestCase  $ assertBool "test23" $ not $ alphaEq p2 $ p6
test24  = TestCase  $ assertBool "test24" $ not $ alphaEq p2 $ p7

test25  = TestCase  $ assertBool "test25" $ not $ alphaEq p3 $ p1
test26  = TestCase  $ assertBool "test26" $ not $ alphaEq p3 $ p2
test27  = TestCase  $ assertBool "test27" $ not $ alphaEq p3 $ belong x y  
test28  = TestCase  $ assertBool "test28" $ not $ alphaEq p3 $ p4
test29  = TestCase  $ assertBool "test29" $ not $ alphaEq p3 $ p5
test30  = TestCase  $ assertBool "test30" $ not $ alphaEq p3 $ p6
test31  = TestCase  $ assertBool "test31" $ not $ alphaEq p3 $ p7
test32  = TestCase  $ assertBool "test32" $ not $ alphaEq p3 $ p8

test33  = TestCase  $ assertBool "test33" $ not $ alphaEq p4 $ p1
test34  = TestCase  $ assertBool "test34" $ not $ alphaEq p4 $ p1
test35  = TestCase  $ assertBool "test35" $ not $ alphaEq p4 $ p1
test36  = TestCase  $ assertBool "test36" $ alphaEq p4 $ forall z (belong z y)
test37  = TestCase  $ assertBool "test37" $ not $ alphaEq p4 $ p5
test38  = TestCase  $ assertBool "test38" $ not $ alphaEq p4 $ p6
test39  = TestCase  $ assertBool "test39" $ not $ alphaEq p4 $ p7
test40  = TestCase  $ assertBool "test40" $ not $ alphaEq p4 $ p8

test41  = TestCase  $ assertBool "test41" $ not $ alphaEq p5 $ p1
test42  = TestCase  $ assertBool "test42" $ not $ alphaEq p5 $ p2
test43  = TestCase  $ assertBool "test43" $ not $ alphaEq p5 $ p3
test44  = TestCase  $ assertBool "test44" $ not $ alphaEq p5 $ p4
test45  = TestCase  $ assertBool "test45" $ not $ alphaEq p5 $ belong x z
test46  = TestCase  $ assertBool "test46" $ not $ alphaEq p5 $ p6
test47  = TestCase  $ assertBool "test47" $ not $ alphaEq p5 $ p7
test48  = TestCase  $ assertBool "test48" $ not $ alphaEq p5 $ p8

test49  = TestCase  $ assertBool "test49" $ not $ alphaEq p6 $ p1
test50  = TestCase  $ assertBool "test50" $ not $ alphaEq p6 $ p2
test51  = TestCase  $ assertBool "test51" $ not $ alphaEq p6 $ p3
test52  = TestCase  $ assertBool "test52" $ not $ alphaEq p6 $ p4
test53  = TestCase  $ assertBool "test53" $ not $ alphaEq p6 $ p5
test54  = TestCase  $ assertBool "test54" $ not $ alphaEq p6 $ belong y z
test55  = TestCase  $ assertBool "test55" $ not $ alphaEq p6 $ p7
test56  = TestCase  $ assertBool "test56" $ not $ alphaEq p6 $ p8

test57  = TestCase  $ assertBool "test57" $ not $ alphaEq p7 $ p1
test58  = TestCase  $ assertBool "test58" $ not $ alphaEq p7 $ p2
test59  = TestCase  $ assertBool "test59" $ not $ alphaEq p7 $ p3
test60  = TestCase  $ assertBool "test60" $ not $ alphaEq p7 $ p4
test61  = TestCase  $ assertBool "test61" $ not $ alphaEq p7 $ p5
test62  = TestCase  $ assertBool "test62" $ not $ alphaEq p7 $ p6
test63  = TestCase  $ assertBool "test63" $ not $ alphaEq p7 $ imply p6 p5
test64  = TestCase  $ assertBool "test64" $ not $ alphaEq p7 $ p8

phi0 = forall t $ imply (belong t x) (belong t y)
test65  = TestCase  $ assertBool "test65" $ not $ alphaEq p8 $ p1
test66  = TestCase  $ assertBool "test66" $ not $ alphaEq p8 $ p2
test67  = TestCase  $ assertBool "test67" $ not $ alphaEq p8 $ p3
test68  = TestCase  $ assertBool "test68" $ not $ alphaEq p8 $ p4
test69  = TestCase  $ assertBool "test69" $ not $ alphaEq p8 $ p5
test70  = TestCase  $ assertBool "test70" $ not $ alphaEq p8 $ p6
test71  = TestCase  $ assertBool "test71" $ not $ alphaEq p8 $ p7
test72  = TestCase  $ assertBool "test72" $       alphaEq p8 $ phi0 


phi1 = forall x $ forall y $ imply (forall y $ belong y x)(forall x $ belong x y)
phi2 = forall x $ forall y $ imply (forall y $ belong y x)(forall z $ belong z y)
phi3 = forall x $ forall t $ imply (forall y $ belong y x)(forall z $ belong z t)
phi4 = forall z $ forall y $ imply (forall x $ belong x z)(forall x $ belong x y)

test73  = TestCase  $ assertBool "test73" $       alphaEq p9 $ p9 
test74  = TestCase  $ assertBool "test74" $       alphaEq p9 $ phi1 
test75  = TestCase  $ assertBool "test75" $       alphaEq p9 $ phi2 
test76  = TestCase  $ assertBool "test76" $       alphaEq p9 $ phi3 
test77  = TestCase  $ assertBool "test77" $       alphaEq p9 $ phi4 

test_AlphaEquiv = TestLabel "test_valid" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  , test41, test42, test43, test44, test45, test46, test47, test48
  , test49, test50, test51, test52, test53, test54, test55, test56
  , test57, test58, test59, test60, test61, test62, test63, test64
  , test65, test66, test67, test68, test69, test70, test71, test72
  , test73, test74, test75, test76, test77
  ]




