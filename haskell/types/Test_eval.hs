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

test21  = TestCase $ assertEqual "eval.21"  (eval t6)   (Nothing)
test22  = TestCase $ assertEqual "eval.22"  (eval t7)   (Nothing)
test23  = TestCase $ assertEqual "eval.23"  (eval t8)   (Just n1)
test24  = TestCase $ assertEqual "eval.24"  (eval t9)   (Just n2)
test25  = TestCase $ assertEqual "eval.25"  (eval t10)  (Just n3)
test26  = TestCase $ assertEqual "eval.26"  (eval' t6)  (Nothing)
test27  = TestCase $ assertEqual "eval.27"  (eval' t7)  (Nothing)
test28  = TestCase $ assertEqual "eval.28"  (eval' t8)  (Just n1)
test29  = TestCase $ assertEqual "eval.29"  (eval' t9)  (Just n2)
test30  = TestCase $ assertEqual "eval.30"  (eval' t10) (Just n3)

-- TmPred

t11 = TmPred t
t12 = TmPred f
t13 = TmPred n0
t14 = TmPred n1
t15 = TmPred n2
t16 = TmPred n3


test31  = TestCase $ assertEqual "eval.31"  (eval t11)  (Nothing)
test32  = TestCase $ assertEqual "eval.32"  (eval t12)  (Nothing)
test33  = TestCase $ assertEqual "eval.33"  (eval t13)  (Just n0)
test34  = TestCase $ assertEqual "eval.34"  (eval t14)  (Just n0)
test35  = TestCase $ assertEqual "eval.35"  (eval t15)  (Just n1)
test36  = TestCase $ assertEqual "eval.36"  (eval t16)  (Just n2)
test37  = TestCase $ assertEqual "eval.37"  (eval' t11) (Nothing)
test38  = TestCase $ assertEqual "eval.38"  (eval' t12) (Nothing)
test39  = TestCase $ assertEqual "eval.39"  (eval' t13) (Just n0)
test40  = TestCase $ assertEqual "eval.40"  (eval' t14) (Just n0)
test41  = TestCase $ assertEqual "eval.41"  (eval' t15) (Just n1)
test42  = TestCase $ assertEqual "eval.42"  (eval' t16) (Just n2)

-- tmIf

t'  = TmIsZero n0
f'  = TmIsZero n1 
t17 = TmIf t' t11 f 
t18 = TmIf t' t12 f 
t19 = TmIf t' t13 f 
t20 = TmIf t' t14 f 
t21 = TmIf t' t15 f 
t22 = TmIf t' t16 f 
t23 = TmIf f' f t11  
t24 = TmIf f' f t12  
t25 = TmIf f' f t13  
t26 = TmIf f' f t14  
t27 = TmIf f' f t15  
t28 = TmIf f' f t16  


test43  = TestCase $ assertEqual "eval.43"  (eval t17) (Nothing)
test44  = TestCase $ assertEqual "eval.44"  (eval t18) (Nothing)
test45  = TestCase $ assertEqual "eval.45"  (eval t19) (Just n0)
test46  = TestCase $ assertEqual "eval.46"  (eval t20) (Just n0)
test47  = TestCase $ assertEqual "eval.47"  (eval t21) (Just n1)
test48  = TestCase $ assertEqual "eval.48"  (eval t22) (Just n2)
test49  = TestCase $ assertEqual "eval.49"  (eval t23) (Nothing)
test50  = TestCase $ assertEqual "eval.50"  (eval t24) (Nothing)
test51  = TestCase $ assertEqual "eval.51"  (eval t25) (Just n0)
test52  = TestCase $ assertEqual "eval.52"  (eval t26) (Just n0)
test53  = TestCase $ assertEqual "eval.53"  (eval t27) (Just n1)
test54  = TestCase $ assertEqual "eval.54"  (eval t28) (Just n2)
test55  = TestCase $ assertEqual "eval.55"  (eval' t17) (Nothing)
test56  = TestCase $ assertEqual "eval.56"  (eval' t18) (Nothing)
test57  = TestCase $ assertEqual "eval.57"  (eval' t19) (Just n0)
test58  = TestCase $ assertEqual "eval.58"  (eval' t20) (Just n0)
test59  = TestCase $ assertEqual "eval.59"  (eval' t21) (Just n1)
test60  = TestCase $ assertEqual "eval.60"  (eval' t22) (Just n2)
test61  = TestCase $ assertEqual "eval.61"  (eval' t23) (Nothing)
test62  = TestCase $ assertEqual "eval.62"  (eval' t24) (Nothing)
test63  = TestCase $ assertEqual "eval.63"  (eval' t25) (Just n0)
test64  = TestCase $ assertEqual "eval.64"  (eval' t26) (Just n0)
test65  = TestCase $ assertEqual "eval.65"  (eval' t27) (Just n1)
test66  = TestCase $ assertEqual "eval.66"  (eval' t28) (Just n2)



test_eval = TestLabel "eval" $ TestList
  [ test1,    test2,    test3,    test4,    test5
  , test6,    test7,    test8,    test9,    test10
  , test11,   test12,   test13,   test14,   test15
  , test16,   test17,   test18,   test19,   test20
  , test21,   test22,   test23,   test24,   test25
  , test26,   test27,   test28,   test29,   test30
  , test31,   test32,   test33,   test34,   test35
  , test36,   test37,   test38,   test39,   test40
  , test41,   test42,   test43,   test44,   test45
  , test46,   test47,   test48,   test49,   test50
  , test51,   test52,   test53,   test54,   test55
  , test56,   test57,   test58,   test59,   test60
  , test61,   test62,   test63,   test64,   test65
  , test66
  ]


