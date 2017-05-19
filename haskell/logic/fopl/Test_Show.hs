module Test_Show
  ( test_Show
  ) where

import Test.HUnit
import Test_data

test1  = TestCase $ assertEqual  "show.1"  (show p1) s1
test2  = TestCase $ assertEqual  "show.2"  (show p2) s2
test3  = TestCase $ assertEqual  "show.3"  (show p3) s3
test4  = TestCase $ assertEqual  "show.4"  (show p4) s4
test5  = TestCase $ assertEqual  "show.5"  (show p5) s5
test6  = TestCase $ assertEqual  "show.6"  (show p6) s6
test7  = TestCase $ assertEqual  "show.7"  (show p7) s7
test8  = TestCase $ assertEqual  "show.8"  (show p8) s8



test_Show = TestLabel "test_Show" $ TestList
  [ test1,    test2,    test3,    test4,  test5
  , test6,    test7,    test8
  ]


