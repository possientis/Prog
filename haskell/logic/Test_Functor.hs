module Test_Functor
  ( test_Functor
  ) where

import Data.Functor ((<$>)) -- for older versions of GHC
import Test.HUnit
import Test_data
import FirstOrder

test1   = TestCase $ assertEqual  "fmap.1"  (f1 <$> p1) q1
test2   = TestCase $ assertEqual  "fmap.2"  (f1 <$> p2) q2
test3   = TestCase $ assertEqual  "fmap.3"  (f1 <$> p3) q3
test4   = TestCase $ assertEqual  "fmap.4"  (f1 <$> p4) q4
test5   = TestCase $ assertEqual  "fmap.5"  (f1 <$> p5) q5
test6   = TestCase $ assertEqual  "fmap.6"  (f1 <$> p6) q6
test7   = TestCase $ assertEqual  "fmap.7"  (f1 <$> p7) q7
test8   = TestCase $ assertEqual  "fmap.8"  (f1 <$> p8) q8

test9   = TestCase $ assertEqual  "fmap.9"  (id <$> p1) p1
test10  = TestCase $ assertEqual  "fmap.10" (id <$> p2) p2
test11  = TestCase $ assertEqual  "fmap.11" (id <$> p3) p3
test12  = TestCase $ assertEqual  "fmap.12" (id <$> p4) p4
test13  = TestCase $ assertEqual  "fmap.13" (id <$> p5) p5
test14  = TestCase $ assertEqual  "fmap.14" (id <$> p6) p6
test15  = TestCase $ assertEqual  "fmap.15" (id <$> p7) p7
test16  = TestCase $ assertEqual  "fmap.16" (id <$> p8) p8



test_Functor = TestLabel "test_Show" $ TestList
  [ test1,    test2,    test3,    test4
  , test5,    test6,    test7,    test8
  , test9,    test10,   test11,   test12
  , test13,   test14,   test15,   test16
  ]


