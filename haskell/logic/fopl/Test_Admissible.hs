module Test_Admissible
  ( test_Admissible
  ) where

import Test.HUnit

import Test_data
import Admissible
import Substitution

test1  = TestCase  $ assertBool "test1"   $ not $ isAdmissibleFor (y<-:x) p1
test2  = TestCase  $ assertBool "test2"   $       isAdmissibleFor (y<-:x) p2
test3  = TestCase  $ assertBool "test3"   $ not $ isAdmissibleFor (y<-:x) p3
test4  = TestCase  $ assertBool "test4"   $ not $ isAdmissibleFor (y<-:x) p4
test5  = TestCase  $ assertBool "test5"   $ not $ isAdmissibleFor (y<-:x) p5
test6  = TestCase  $ assertBool "test6"   $       isAdmissibleFor (y<-:x) p6
test7  = TestCase  $ assertBool "test7"   $ not $ isAdmissibleFor (y<-:x) p7
test8  = TestCase  $ assertBool "test8"   $ not $ isAdmissibleFor (y<-:x) p8

test9  = TestCase  $ assertBool "test9"   $ not $ isAdmissibleFor (z<-:x) p1
test10 = TestCase  $ assertBool "test10"  $       isAdmissibleFor (z<-:x) p2
test11 = TestCase  $ assertBool "test11"  $ not $ isAdmissibleFor (z<-:x) p3
test12 = TestCase  $ assertBool "test12"  $       isAdmissibleFor (z<-:x) p4
test13 = TestCase  $ assertBool "test13"  $ not $ isAdmissibleFor (z<-:x) p5
test14 = TestCase  $ assertBool "test14"  $       isAdmissibleFor (z<-:x) p6
test15 = TestCase  $ assertBool "test15"  $ not $ isAdmissibleFor (z<-:x) p7
test16 = TestCase  $ assertBool "test16"  $ not $ isAdmissibleFor (z<-:x) p8

test17  = TestCase  $ assertBool "test17" $       isAdmissibleFor (x<-:x) p1
test18  = TestCase  $ assertBool "test18" $       isAdmissibleFor (x<-:x) p2
test19  = TestCase  $ assertBool "test19" $       isAdmissibleFor (x<-:x) p3
test20  = TestCase  $ assertBool "test20" $       isAdmissibleFor (x<-:x) p4
test21  = TestCase  $ assertBool "test21" $       isAdmissibleFor (x<-:x) p5
test22  = TestCase  $ assertBool "test22" $       isAdmissibleFor (x<-:x) p6
test23  = TestCase  $ assertBool "test23" $       isAdmissibleFor (x<-:x) p7
test24  = TestCase  $ assertBool "test24" $       isAdmissibleFor (x<-:x) p8

test25  = TestCase  $ assertBool "test25" $ not $ isAdmissibleFor (x<-:y) p1
test26  = TestCase  $ assertBool "test26" $       isAdmissibleFor (x<-:y) p2
test27  = TestCase  $ assertBool "test27" $ not $ isAdmissibleFor (x<-:y) p3
test28  = TestCase  $ assertBool "test28" $ not $ isAdmissibleFor (x<-:y) p4
test29  = TestCase  $ assertBool "test29" $       isAdmissibleFor (x<-:y) p5
test30  = TestCase  $ assertBool "test30" $ not $ isAdmissibleFor (x<-:y) p6
test31  = TestCase  $ assertBool "test31" $ not $ isAdmissibleFor (x<-:y) p7
test32  = TestCase  $ assertBool "test32" $ not $ isAdmissibleFor (x<-:y) p8

test33  = TestCase  $ assertBool "test33" $       isAdmissibleFor (y<-:y) p1
test34  = TestCase  $ assertBool "test34" $       isAdmissibleFor (y<-:y) p2
test35  = TestCase  $ assertBool "test35" $       isAdmissibleFor (y<-:y) p3
test36  = TestCase  $ assertBool "test36" $       isAdmissibleFor (y<-:y) p4
test37  = TestCase  $ assertBool "test37" $       isAdmissibleFor (y<-:y) p5
test38  = TestCase  $ assertBool "test38" $       isAdmissibleFor (y<-:y) p6
test39  = TestCase  $ assertBool "test39" $       isAdmissibleFor (y<-:y) p7
test40  = TestCase  $ assertBool "test40" $       isAdmissibleFor (y<-:y) p8

test41  = TestCase  $ assertBool "test41" $ not $ isAdmissibleFor (z<-:y) p1
test42  = TestCase  $ assertBool "test42" $       isAdmissibleFor (z<-:y) p2
test43  = TestCase  $ assertBool "test43" $ not $ isAdmissibleFor (z<-:y) p3
test44  = TestCase  $ assertBool "test44" $ not $ isAdmissibleFor (z<-:y) p4
test45  = TestCase  $ assertBool "test45" $       isAdmissibleFor (z<-:y) p5
test46  = TestCase  $ assertBool "test46" $ not $ isAdmissibleFor (z<-:y) p6
test47  = TestCase  $ assertBool "test47" $ not $ isAdmissibleFor (z<-:y) p7
test48  = TestCase  $ assertBool "test48" $ not $ isAdmissibleFor (z<-:y) p8

test49  = TestCase  $ assertBool "test49" $       isAdmissibleFor (x<-:z) p1
test50  = TestCase  $ assertBool "test50" $       isAdmissibleFor (x<-:z) p2
test51  = TestCase  $ assertBool "test51" $       isAdmissibleFor (x<-:z) p3
test52  = TestCase  $ assertBool "test52" $       isAdmissibleFor (x<-:z) p4
test53  = TestCase  $ assertBool "test53" $ not $ isAdmissibleFor (x<-:z) p5
test54  = TestCase  $ assertBool "test54" $ not $ isAdmissibleFor (x<-:z) p6
test55  = TestCase  $ assertBool "test55" $ not $ isAdmissibleFor (x<-:z) p7
test56  = TestCase  $ assertBool "test56" $ not $ isAdmissibleFor (x<-:z) p8

test57  = TestCase  $ assertBool "test57" $       isAdmissibleFor (y<-:z) p1
test58  = TestCase  $ assertBool "test58" $       isAdmissibleFor (y<-:z) p2
test59  = TestCase  $ assertBool "test59" $       isAdmissibleFor (y<-:z) p3
test60  = TestCase  $ assertBool "test60" $       isAdmissibleFor (y<-:z) p4
test61  = TestCase  $ assertBool "test61" $ not $ isAdmissibleFor (y<-:z) p5
test62  = TestCase  $ assertBool "test62" $ not $ isAdmissibleFor (y<-:z) p6
test63  = TestCase  $ assertBool "test63" $ not $ isAdmissibleFor (y<-:z) p7
test64  = TestCase  $ assertBool "test64" $ not $ isAdmissibleFor (y<-:z) p8


test_Admissible = TestLabel "test_admissible" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  , test41, test42, test43, test44, test45, test46, test47, test48
  , test49, test50, test51, test52, test53, test54, test55, test56
  , test57, test58, test59, test60, test61, test62, test63, test64
  ]


