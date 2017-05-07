import Term
import Test.HUnit

t1 = TmIsZero (TmPred (TmSucc TmZero))
t2 = TmIf t1 TmTrue TmZero
t3 = TmIf TmFalse TmTrue  TmZero

test1 = TestCase $ assertEqual "eval1.1" s1 s2 where
  s1 = eval1 $ TmIf TmTrue t2 t3
  s2 = Just t2 

test2 = TestCase $ assertEqual "eval1.2" s1 s2 where
  s1 = eval1 $ TmIf TmFalse t2 t3
  s2 = Just t3

test3 = TestCase $ assertEqual "eval1.3" s1 s2 where
  s1 = eval1  $ TmIf t1 t2 t3
  s2 = Just   $ TmIf (TmIsZero TmZero) t2 t3

test4 = TestCase $ assertEqual "eval1.4" s1 s2 where
  s1 = eval1  $ TmSucc (TmPred (TmSucc TmZero))
  s2 = Just   $ TmSucc TmZero

test5 = TestCase $ assertEqual "eval1.5" s1 s2 where
  s1 = eval1  $ TmPred TmZero
  s2 = Just   $ TmZero

test6 = TestCase $ assertEqual "eval1.6" s1 s2 where
  s1 = eval1  $ TmPred (TmSucc (TmSucc TmZero))
  s2 = Just   $ TmSucc TmZero 

test7 = TestCase $ assertEqual "eval1.7" s1 s2 where
  s1 = eval1  $ TmPred (TmSucc (TmSucc TmTrue))
  s2 = Nothing

test8 = TestCase $ assertEqual "eval1.8" s1 s2 where
  s1 = eval1  $ TmPred (TmIf TmTrue TmZero (TmSucc TmZero))
  s2 = Just   $ TmPred TmZero

test9 = TestCase $ assertEqual "eval1.9" s1 s2 where
  s1 = eval1  $ TmIsZero TmZero
  s2 = Just   $ TmTrue

test10 = TestCase $ assertEqual "eval1.10" s1 s2 where
  s1 = eval1  $ TmIsZero (TmSucc TmZero)
  s2 = Just   $ TmFalse

test11 = TestCase $ assertEqual "eval1.11" s1 s2 where
  s1 = eval1  $ TmIsZero (TmSucc TmTrue)
  s2 = Nothing

test12 = TestCase $ assertEqual "eval1.12" s1 s2 where
  s1 = eval1  $ TmIsZero (TmPred (TmSucc TmZero))
  s2 = Just   $ TmIsZero TmZero

test_eval1 = TestLabel "eval1" $ TestList 
  [ test1,  test2,  test3,  test4,  test5,  test6 
  , test7,  test8,  test9,  test10, test11, test12
  ]

tests = TestList 
      [ test_eval1
      ]


main = do
  runTestTT tests
