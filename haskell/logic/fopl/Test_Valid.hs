module Test_Valid
  ( test_Valid
  ) where

import Test.HUnit

import Test_data
import Valid
import Substitution

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

-- f4 z = f4 y, so f4 not valid for Az.(z:x -> z:y)
test25  = TestCase  $ assertBool "test25" $ isValidFor f4 p1
test26  = TestCase  $ assertBool "test26" $ isValidFor f4 p2
test27  = TestCase  $ assertBool "test27" $ isValidFor f4 p3
test28  = TestCase  $ assertBool "test28" $ isValidFor f4 p4
test29  = TestCase  $ assertBool "test29" $ isValidFor f4 p5
test30  = TestCase  $ assertBool "test30" $ isValidFor f4 p6
test31  = TestCase  $ assertBool "test31" $ isValidFor f4 p7
test32  = TestCase  $ assertBool "test32" $ not $ isValidFor f4 p8

-- (y<-:x) x = (y<-:x) y, so y<-:x is not valid for Ax.x:y
test33  = TestCase  $ assertBool "test33" $ isValidFor (y<-:x) p1
test34  = TestCase  $ assertBool "test34" $ isValidFor (y<-:x) p2
test35  = TestCase  $ assertBool "test35" $ isValidFor (y<-:x) p3
test36  = TestCase  $ assertBool "test36" $ not $ isValidFor (y<-:x) p4
test37  = TestCase  $ assertBool "test37" $ isValidFor (y<-:x) p5
test38  = TestCase  $ assertBool "test38" $ isValidFor (y<-:x) p6
test39  = TestCase  $ assertBool "test39" $ isValidFor (y<-:x) p7
test40  = TestCase  $ assertBool "test40" $ isValidFor (y<-:x) p8

-- (z<-:x) is not valid for Az.(z:x -> z:y)
test41  = TestCase  $ assertBool "test41" $ isValidFor (z<-:x) p1
test42  = TestCase  $ assertBool "test42" $ isValidFor (z<-:x) p2
test43  = TestCase  $ assertBool "test43" $ isValidFor (z<-:x) p3
test44  = TestCase  $ assertBool "test44" $ isValidFor (z<-:x) p4
test45  = TestCase  $ assertBool "test45" $ isValidFor (z<-:x) p5
test46  = TestCase  $ assertBool "test46" $ isValidFor (z<-:x) p6
test47  = TestCase  $ assertBool "test47" $ isValidFor (z<-:x) p7
test48  = TestCase  $ assertBool "test48" $ not $ isValidFor (z<-:x) p8

-- (z<-:y) is not valid for Az.(z:x -> z:y)
test49  = TestCase  $ assertBool "test49" $ isValidFor (z<-:y) p1
test50  = TestCase  $ assertBool "test50" $ isValidFor (z<-:y) p2
test51  = TestCase  $ assertBool "test51" $ isValidFor (z<-:y) p3
test52  = TestCase  $ assertBool "test52" $ isValidFor (z<-:y) p4
test53  = TestCase  $ assertBool "test53" $ isValidFor (z<-:y) p5
test54  = TestCase  $ assertBool "test54" $ isValidFor (z<-:y) p6
test55  = TestCase  $ assertBool "test55" $ isValidFor (z<-:y) p7
test56  = TestCase  $ assertBool "test56" $ not $ isValidFor (z<-:y) p8

-- (x<->y) is injective hence always valid for any formula
test57  = TestCase  $ assertBool "test57" $ isValidFor (x<->y) p1
test58  = TestCase  $ assertBool "test58" $ isValidFor (x<->y) p2
test59  = TestCase  $ assertBool "test59" $ isValidFor (x<->y) p3
test60  = TestCase  $ assertBool "test60" $ isValidFor (x<->y) p4
test61  = TestCase  $ assertBool "test61" $ isValidFor (x<->y) p5
test62  = TestCase  $ assertBool "test62" $ isValidFor (x<->y) p6
test63  = TestCase  $ assertBool "test63" $ isValidFor (x<->y) p7
test64  = TestCase  $ assertBool "test64" $ isValidFor (x<->y) p8


test65  = TestCase  $ assertBool "test65" $ isValidFor f1 p9
test66  = TestCase  $ assertBool "test66" $ not $ isValidFor f2 p9
test67  = TestCase  $ assertBool "test67" $ not $ isValidFor f3 p9
test68  = TestCase  $ assertBool "test68" $ isValidFor f4 p9
test69  = TestCase  $ assertBool "test69" $ not $ isValidFor (y<-:x) p9
test70  = TestCase  $ assertBool "test70" $ not $ isValidFor (x<-:y) p9
test71  = TestCase  $ assertBool "test71" $ not $ isValidFor (x<-:z) p9
test72  = TestCase  $ assertBool "test72" $ not $ isValidFor (z<-:x) p9
test73  = TestCase  $ assertBool "test73" $ isValidFor (z<-:y) p9
test74  = TestCase  $ assertBool "test74" $ isValidFor (y<-:z) p9
test75  = TestCase  $ assertBool "test75" $ isValidFor (y<->x) p9
test76  = TestCase  $ assertBool "test76" $ isValidFor (x<->y) p9
test77  = TestCase  $ assertBool "test77" $ isValidFor (z<->x) p9
test78  = TestCase  $ assertBool "test78" $ isValidFor (x<->z) p9
test79  = TestCase  $ assertBool "test79" $ isValidFor (y<->z) p9
test80  = TestCase  $ assertBool "test80" $ isValidFor (z<->y) p9

test_Valid = TestLabel "test_valid" $ TestList
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
  ]


