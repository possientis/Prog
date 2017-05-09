module Test_eval
  ( test_eval
  ) where

import Term
import Test.HUnit

t1 = TmIsZero (TmPred (TmSucc TmZero))
t2 = TmIf t1 TmTrue TmZero
t3 = TmIf TmFalse TmTrue  TmZero

test1 = TestCase $ assertEqual "eval1.1" s1 s2 where
  s1 = eval1 $ TmIf TmTrue t2 t3
  s2 = Just t2 



test_eval = TestLabel "eval" $ TestList
  [
  ]


