module Test_eval
  ( test_eval
  ) where

import Term
import Test.HUnit

-- values

t = TmTrue
f = TmFalse
n0 = TmZero
n1 = TmSucc n0
n2 = TmSucc n1
n3 = TmSucc n2

test1   = TestCase $ assertEqual "eval.1"   (eval t)    (Just t) 
test2   = TestCase $ assertEqual "eval.2"   (eval f)    (Just f) 
test3   = TestCase $ assertEqual "eval.3"   (eval n0)   (Just n0) 
test4   = TestCase $ assertEqual "eval.4"   (eval n1)   (Just n1) 
test5   = TestCase $ assertEqual "eval.5"   (eval n2)   (Just n2) 
test6   = TestCase $ assertEqual "eval.6"   (eval' t)   (Just t) 
test7   = TestCase $ assertEqual "eval.7"   (eval' f)   (Just f) 
test8   = TestCase $ assertEqual "eval.8"   (eval' n0)  (Just n0) 
test9   = TestCase $ assertEqual "eval.9"   (eval' n1)  (Just n1) 
test10  = TestCase $ assertEqual "eval.10"  (eval' n2)  (Just n2) 

-- TmIsZero

t1 = TmIsZero t
t2 = TmIsZero f
t3 = TmIsZero n0
t4 = TmIsZero n1
t5 = TmIsZero n2

test11  = TestCase $ assertEqual "eval.11"  (eval t1)   (Nothing)
test12  = TestCase $ assertEqual "eval.12"  (eval t2)   (Nothing)
test13  = TestCase $ assertEqual "eval.13"  (eval t3)   (Just TmTrue)
test14  = TestCase $ assertEqual "eval.14"  (eval t4)   (Just TmFalse)
test15  = TestCase $ assertEqual "eval.15"  (eval t5)   (Just TmFalse)
test16  = TestCase $ assertEqual "eval.16"  (eval' t1)  (Nothing)
test17  = TestCase $ assertEqual "eval.17"  (eval' t2)  (Nothing)
test18  = TestCase $ assertEqual "eval.18"  (eval' t3)  (Just TmTrue)
test19  = TestCase $ assertEqual "eval.19"  (eval' t4)  (Just TmFalse)
test20  = TestCase $ assertEqual "eval.20"  (eval' t5)  (Just TmFalse)


-- TmSucc

t6  = TmSucc t
t7  = TmSucc f
t8  = TmSucc n0
t9  = TmSucc n1
t10 = TmSucc n2 

test21  = TestCase $ assertEqual "eval.21"  (eval t6)  (Nothing)
test22  = TestCase $ assertEqual "eval.22"  (eval t7)  (Nothing)
test23  = TestCase $ assertEqual "eval.23"  (eval t8)  (Just n1)
test24  = TestCase $ assertEqual "eval.24"  (eval t9)  (Just n2)
test25  = TestCase $ assertEqual "eval.25"  (eval t10) (Just n3)
test26  = TestCase $ assertEqual "eval.26"  (eval' t6) (Nothing)
test27  = TestCase $ assertEqual "eval.27"  (eval' t7) (Nothing)
test28  = TestCase $ assertEqual "eval.28"  (eval' t8) (Just n1)
test29  = TestCase $ assertEqual "eval.29"  (eval' t9) (Just n2)
test30  = TestCase $ assertEqual "eval.30"  (eval' t10)(Just n3)



test_eval = TestLabel "eval" $ TestList
  [ test1,    test2,    test3,    test4,    test5
  , test6,    test7,    test8,    test9,    test10
  , test11,   test12,   test13,   test14,   test15
  , test16,   test17,   test18,   test19,   test20
  , test21,   test22,   test23,   test24,   test25
  , test26,   test27,   test28,   test29,   test30
  ]



