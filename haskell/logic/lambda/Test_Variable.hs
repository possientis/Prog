module Test_Variable
  ( test_Variable
  ) where

import Test.HUnit
import Data.Set
import Data.Functor ((<$>))

import Test_data
import Variable
import Prelude hiding (map) -- conflicts with Data.Set

test1 = TestCase $ assertEqual "test1" (var p1) var1 
test2 = TestCase $ assertEqual "test2" (var p2) var2
test3 = TestCase $ assertEqual "test3" (var p3) var3
test4 = TestCase $ assertEqual "test4" (var p4) var4
test5 = TestCase $ assertEqual "test5" (var p5) var5
test6 = TestCase $ assertEqual "test6" (var p6) var6
test7 = TestCase $ assertEqual "test7" (var p7) var7
test8 = TestCase $ assertEqual "test8" (var p8) var8

-- var (f p) = f[var p] (direct image) 
test9   = TestCase $ assertEqual "test9"  (var $ f1 <$> p1) (map f1 var1) 
test10  = TestCase $ assertEqual "test10" (var $ f1 <$> p2) (map f1 var2) 
test11  = TestCase $ assertEqual "test11" (var $ f1 <$> p3) (map f1 var3) 
test12  = TestCase $ assertEqual "test12" (var $ f1 <$> p4) (map f1 var4) 
test13  = TestCase $ assertEqual "test13" (var $ f1 <$> p5) (map f1 var5) 
test14  = TestCase $ assertEqual "test14" (var $ f1 <$> p6) (map f1 var6) 
test15  = TestCase $ assertEqual "test15" (var $ f1 <$> p7) (map f1 var7) 
test16  = TestCase $ assertEqual "test16" (var $ f1 <$> p8) (map f1 var8) 

test17   = TestCase $ assertEqual "test17" (free p1) free1 
test18   = TestCase $ assertEqual "test18" (free p2) free2
test19   = TestCase $ assertEqual "test19" (free p3) free3
test20   = TestCase $ assertEqual "test20" (free p4) free4
test21   = TestCase $ assertEqual "test21" (free p5) free5
test22   = TestCase $ assertEqual "test22" (free p6) free6
test23   = TestCase $ assertEqual "test23" (free p7) free7
test24   = TestCase $ assertEqual "test24" (free p8) free8

-- free (f p) = f[free p] (direct image) for f|(var p) injective
test25  = TestCase $ assertEqual "test25" (free $ f1 <$> p1) (map f1 free1) 
test26  = TestCase $ assertEqual "test26" (free $ f1 <$> p2) (map f1 free2) 
test27  = TestCase $ assertEqual "test27" (free $ f1 <$> p3) (map f1 free3) 
test28  = TestCase $ assertEqual "test28" (free $ f1 <$> p4) (map f1 free4) 
test29  = TestCase $ assertEqual "test29" (free $ f1 <$> p5) (map f1 free5) 
test30  = TestCase $ assertEqual "test30" (free $ f1 <$> p6) (map f1 free6) 
test31  = TestCase $ assertEqual "test31" (free $ f1 <$> p7) (map f1 free7) 
test32  = TestCase $ assertEqual "test32" (free $ f1 <$> p8) (map f1 free8) 


test_Variable = TestLabel "test_var" $ TestList 
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  ]
