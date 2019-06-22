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

test65  = TestCase  $ assertBool "test65" $       isAdmissibleFor (z<-:z) p1
test66  = TestCase  $ assertBool "test66" $       isAdmissibleFor (z<-:z) p2
test67  = TestCase  $ assertBool "test67" $       isAdmissibleFor (z<-:z) p3
test68  = TestCase  $ assertBool "test68" $       isAdmissibleFor (z<-:z) p4
test69  = TestCase  $ assertBool "test69" $       isAdmissibleFor (z<-:z) p5
test70  = TestCase  $ assertBool "test70" $       isAdmissibleFor (z<-:z) p6
test71  = TestCase  $ assertBool "test71" $       isAdmissibleFor (z<-:z) p7
test72  = TestCase  $ assertBool "test72" $       isAdmissibleFor (z<-:z) p8

test73  = TestCase  $ assertBool "test73" $       isAdmissibleFor (x<->x) p1
test74  = TestCase  $ assertBool "test74" $       isAdmissibleFor (x<->x) p2
test75  = TestCase  $ assertBool "test75" $       isAdmissibleFor (x<->x) p3
test76  = TestCase  $ assertBool "test76" $       isAdmissibleFor (x<->x) p4
test77  = TestCase  $ assertBool "test77" $       isAdmissibleFor (x<->x) p5
test78  = TestCase  $ assertBool "test78" $       isAdmissibleFor (x<->x) p6
test79  = TestCase  $ assertBool "test79" $       isAdmissibleFor (x<->x) p7
test80  = TestCase  $ assertBool "test80" $       isAdmissibleFor (x<->x) p8

test81  = TestCase  $ assertBool "test81" $ not $ isAdmissibleFor (y<->x) p1
test82  = TestCase  $ assertBool "test82" $       isAdmissibleFor (y<->x) p2
test83  = TestCase  $ assertBool "test83" $ not $ isAdmissibleFor (y<->x) p3
test84  = TestCase  $ assertBool "test84" $ not $ isAdmissibleFor (y<->x) p4
test85  = TestCase  $ assertBool "test85" $ not $ isAdmissibleFor (y<->x) p5
test86  = TestCase  $ assertBool "test86" $ not $ isAdmissibleFor (y<->x) p6
test87  = TestCase  $ assertBool "test87" $ not $ isAdmissibleFor (y<->x) p7
test88  = TestCase  $ assertBool "test88" $ not $ isAdmissibleFor (y<->x) p8

test89  = TestCase  $ assertBool "test89" $ not $ isAdmissibleFor (z<->x) p1
test90  = TestCase  $ assertBool "test90" $       isAdmissibleFor (z<->x) p2
test91  = TestCase  $ assertBool "test91" $ not $ isAdmissibleFor (z<->x) p3
test92  = TestCase  $ assertBool "test92" $       isAdmissibleFor (z<->x) p4
test93  = TestCase  $ assertBool "test93" $ not $ isAdmissibleFor (z<->x) p5
test94  = TestCase  $ assertBool "test94" $ not $ isAdmissibleFor (z<->x) p6
test95  = TestCase  $ assertBool "test95" $ not $ isAdmissibleFor (z<->x) p7
test96  = TestCase  $ assertBool "test96" $ not $ isAdmissibleFor (z<->x) p8

test97  = TestCase  $ assertBool "test97" $ not $ isAdmissibleFor (x<->y) p1
test98  = TestCase  $ assertBool "test98" $       isAdmissibleFor (x<->y) p2
test99  = TestCase  $ assertBool "test99" $ not $ isAdmissibleFor (x<->y) p3
test100 = TestCase  $ assertBool "test100"$ not $ isAdmissibleFor (x<->y) p4
test101 = TestCase  $ assertBool "test101"$ not $ isAdmissibleFor (x<->y) p5
test102 = TestCase  $ assertBool "test102"$ not $ isAdmissibleFor (x<->y) p6
test103 = TestCase  $ assertBool "test103"$ not $ isAdmissibleFor (x<->y) p7
test104 = TestCase  $ assertBool "test104"$ not $ isAdmissibleFor (x<->y) p8


test105 = TestCase  $ assertBool "test105"$       isAdmissibleFor (y<->y) p1
test106 = TestCase  $ assertBool "test106"$       isAdmissibleFor (y<->y) p2
test107 = TestCase  $ assertBool "test107"$       isAdmissibleFor (y<->y) p3
test108 = TestCase  $ assertBool "test108"$       isAdmissibleFor (y<->y) p4
test109 = TestCase  $ assertBool "test109"$       isAdmissibleFor (y<->y) p5
test110 = TestCase  $ assertBool "test110"$       isAdmissibleFor (y<->y) p6
test111 = TestCase  $ assertBool "test111"$       isAdmissibleFor (y<->y) p7
test112 = TestCase  $ assertBool "test112"$       isAdmissibleFor (y<->y) p8

test113 = TestCase  $ assertBool "test113"$ not $ isAdmissibleFor (z<->y) p1
test114 = TestCase  $ assertBool "test114"$       isAdmissibleFor (z<->y) p2
test115 = TestCase  $ assertBool "test115"$ not $ isAdmissibleFor (z<->y) p3
test116 = TestCase  $ assertBool "test116"$ not $ isAdmissibleFor (z<->y) p4
test117 = TestCase  $ assertBool "test117"$ not $ isAdmissibleFor (z<->y) p5
test118 = TestCase  $ assertBool "test118"$ not $ isAdmissibleFor (z<->y) p6
test119 = TestCase  $ assertBool "test119"$ not $ isAdmissibleFor (z<->y) p7
test120 = TestCase  $ assertBool "test120"$ not $ isAdmissibleFor (z<->y) p8

test121 = TestCase  $ assertBool "test121"$ not $ isAdmissibleFor (x<->z) p1
test122 = TestCase  $ assertBool "test122"$       isAdmissibleFor (x<->z) p2
test123 = TestCase  $ assertBool "test123"$ not $ isAdmissibleFor (x<->z) p3
test124 = TestCase  $ assertBool "test124"$       isAdmissibleFor (x<->z) p4
test125 = TestCase  $ assertBool "test125"$ not $ isAdmissibleFor (x<->z) p5
test126 = TestCase  $ assertBool "test126"$ not $ isAdmissibleFor (x<->z) p6
test127 = TestCase  $ assertBool "test127"$ not $ isAdmissibleFor (x<->z) p7
test128 = TestCase  $ assertBool "test128"$ not $ isAdmissibleFor (x<->z) p8

test129 = TestCase  $ assertBool "test129"$ not $ isAdmissibleFor (y<->z) p1
test130 = TestCase  $ assertBool "test130"$       isAdmissibleFor (y<->z) p2
test131 = TestCase  $ assertBool "test131"$ not $ isAdmissibleFor (y<->z) p3
test132 = TestCase  $ assertBool "test132"$ not $ isAdmissibleFor (y<->z) p4
test133 = TestCase  $ assertBool "test133"$ not $ isAdmissibleFor (y<->z) p5
test134 = TestCase  $ assertBool "test134"$ not $ isAdmissibleFor (y<->z) p6
test135 = TestCase  $ assertBool "test135"$ not $ isAdmissibleFor (y<->z) p7
test136 = TestCase  $ assertBool "test136"$ not $ isAdmissibleFor (y<->z) p8

test137 = TestCase  $ assertBool "test137"$       isAdmissibleFor (z<->z) p1
test138 = TestCase  $ assertBool "test138"$       isAdmissibleFor (z<->z) p2
test139 = TestCase  $ assertBool "test139"$       isAdmissibleFor (z<->z) p3
test140 = TestCase  $ assertBool "test140"$       isAdmissibleFor (z<->z) p4
test141 = TestCase  $ assertBool "test141"$       isAdmissibleFor (z<->z) p5
test142 = TestCase  $ assertBool "test142"$       isAdmissibleFor (z<->z) p6
test143 = TestCase  $ assertBool "test143"$       isAdmissibleFor (z<->z) p7
test144 = TestCase  $ assertBool "test144"$       isAdmissibleFor (z<->z) p8

test_Admissible = TestLabel "test_admissible" $ TestList
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
  , test89, test90, test91, test92, test93, test94, test95, test96
  , test97, test98, test99, test100,test101,test102,test103,test104
  , test105,test106,test107,test108,test109,test110,test111,test112
  , test113,test114,test115,test116,test117,test118,test119,test120
  , test121,test122,test123,test124,test125,test126,test127,test128
  , test129,test130,test131,test132,test133,test134,test135,test136
  , test137,test138,test139,test140,test141,test142,test143,test144
  ]


