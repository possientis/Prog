module Test_Functor
  ( test_Functor
  ) where

import Test.HUnit
import Test_data
import FirstOrder

test1  = TestCase $ assertEqual  "fmap.1"  (f1 <$> p1) (belong 0 1) 
test2  = TestCase $ assertEqual  "fmap.2"  (f1 <$> p2) (bot)
test3  = TestCase $ assertEqual  "fmap.3"  (f1 <$> p3) $ imply (belong 0 1) bot
test4  = TestCase $ assertEqual  "fmap.4"  (f1 <$> p4) $ forall 0 (belong 0 1)
test5  = TestCase $ assertEqual  "fmap.5"  (id <$> p1) p1
test6  = TestCase $ assertEqual  "fmap.6"  (id <$> p2) p2
test7  = TestCase $ assertEqual  "fmap.7"  (id <$> p3) p3
test8  = TestCase $ assertEqual  "fmap.8"  (id <$> p4) p4



test_Functor = TestLabel "test_Show" $ TestList
  [ test1,    test2,    test3,    test4,
    test5,    test6,    test7,    test8
  ]


