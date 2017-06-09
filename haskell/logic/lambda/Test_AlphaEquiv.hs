module Test_AlphaEquiv
  ( test_AlphaEquiv
  ) where

import Test.HUnit

import Data.Functor ((<$>))
import Test_data
import AlphaEquiv
import Formula
import V
import Substitution

test1   = TestCase  $ assertBool "test1"  $ alphaEq p1 p1
test2   = TestCase  $ assertBool "test2"  $ alphaEq p2 p2
test3   = TestCase  $ assertBool "test3"  $ alphaEq p3 p3
test4   = TestCase  $ assertBool "test4"  $ alphaEq p4 p4
test5   = TestCase  $ assertBool "test5"  $ alphaEq p5 p5
test6   = TestCase  $ assertBool "test6"  $ alphaEq p6 p6
test7   = TestCase  $ assertBool "test7"  $ alphaEq p7 p7
test8   = TestCase  $ assertBool "test8"  $ alphaEq p8 p8

test9   = TestCase  $ assertBool "test9"  $       alphaEq p1 $ variable x
test10  = TestCase  $ assertBool "test10" $ not $ alphaEq p1 $ variable y
test11  = TestCase  $ assertBool "test11" $ not $ alphaEq p1 $ variable z
test12  = TestCase  $ assertBool "test12" $ not $ alphaEq p1 $ p3
test13  = TestCase  $ assertBool "test13" $ not $ alphaEq p1 $ p4
test14  = TestCase  $ assertBool "test14" $ not $ alphaEq p1 $ p5
test15  = TestCase  $ assertBool "test15" $ not $ alphaEq p1 $ p6
test16  = TestCase  $ assertBool "test16" $ not $ alphaEq p1 $ p7

test17  = TestCase  $ assertBool "test17" $ not $ alphaEq p2 $ p1
test18  = TestCase  $ assertBool "test18" $       alphaEq p2 $ variable y
test19  = TestCase  $ assertBool "test19" $ not $ alphaEq p2 $ p3
test20  = TestCase  $ assertBool "test20" $ not $ alphaEq p2 $ p4
test21  = TestCase  $ assertBool "test21" $ not $ alphaEq p2 $ p5 
test22  = TestCase  $ assertBool "test22" $ not $ alphaEq p2 $ p6
test23  = TestCase  $ assertBool "test23" $ not $ alphaEq p2 $ p7
test24  = TestCase  $ assertBool "test24" $ not $ alphaEq p2 $ p8

test25  = TestCase  $ assertBool "test25" $ not $ alphaEq p3 $ p1
test26  = TestCase  $ assertBool "test26" $ not $ alphaEq p3 $ p2
test27  = TestCase  $ assertBool "test27" $ not $ alphaEq p3 $ variable x
test28  = TestCase  $ assertBool "test28" $ not $ alphaEq p3 $ p4
test29  = TestCase  $ assertBool "test29" $ not $ alphaEq p3 $ p5
test30  = TestCase  $ assertBool "test30" $ not $ alphaEq p3 $ p6
test31  = TestCase  $ assertBool "test31" $ not $ alphaEq p3 $ p7
test32  = TestCase  $ assertBool "test32" $ not $ alphaEq p3 $ p8

test33  = TestCase  $ assertBool "test33" $ not $ alphaEq p4 $ p1
test34  = TestCase  $ assertBool "test34" $ not $ alphaEq p4 $ p2
test35  = TestCase  $ assertBool "test35" $ not $ alphaEq p4 $ p3
test36  = TestCase  $ assertBool "test36" $ alphaEq p4 $ lambda z (variable z)
test37  = TestCase  $ assertBool "test37" $ not $ alphaEq p4 $ p5
test38  = TestCase  $ assertBool "test38" $ not $ alphaEq p4 $ p6
test39  = TestCase  $ assertBool "test39" $ not $ alphaEq p4 $ p7
test40  = TestCase  $ assertBool "test40" $ not $ alphaEq p4 $ p8

test41  = TestCase  $ assertBool "test41" $ not $ alphaEq p5 $ p6
test42  = TestCase  $ assertBool "test42" $ not $ alphaEq p5 $ p7
test43  = TestCase  $ assertBool "test43" $ not $ alphaEq p5 $ ((y<-:x) <$> p5)
test44  = TestCase  $ assertBool "test44" $ not $ alphaEq p5 $ ((x<-:y) <$> p5)
test45  = TestCase  $ assertBool "test45"       $ alphaEq p5 $ ((x<->y) <$> p5)
test46  = TestCase  $ assertBool "test46"       $ alphaEq p5 $ ((z<-:x) <$> p5)
test47  = TestCase  $ assertBool "test47"       $ alphaEq p5 $ ((y<->z) <$> p5)
test48  = TestCase  $ assertBool "test48"       $ alphaEq p5 $ ((t<-:y) <$> p5)


test_AlphaEquiv = TestLabel "test_valid" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  , test41, test42, test43, test44, test45, test46, test47, test48
{-  , test49, test50, test51, test52, test53, test54, test55, test56
  , test57, test58, test59, test60, test61, test62, test63, test64
  , test65, test66, test67, test68, test69, test70, test71, test72
  , test73, test74, test75, test76, test77, test78, test79, test80
  , test81, test82, test83, test84, test85, test86, test87, test88
  , test89, test90, test91, test92, test93, test94, test95, test96
-}  ]



