module Test_Show
  ( test_Show
  ) where

import Test.HUnit
import Test_data

test1  = TestCase $ assertEqual  "show.1"  (show p1) "x:y"
test2  = TestCase $ assertEqual  "show.2"  (show p2) "!"
test3  = TestCase $ assertEqual  "show.3"  (show p3) "(x:y -> !)"
test4  = TestCase $ assertEqual  "show.4"  (show p4) "Ax.x:y"



test_Show = TestLabel "test_Show" $ TestList
  [ test1,    test2,    test3,    test4
  ]


