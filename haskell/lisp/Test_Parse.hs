module Test_Parse
  ( test_Parse
  ) where


import Test.HUnit
import Parse

test1   = TestCase  $ assertEqual "test1"   (check symbol "!abc")   (Just '!') 
test2   = TestCase  $ assertEqual "test2"   (check symbol "$abc")   (Just '$') 
test3   = TestCase  $ assertEqual "test3"   (check symbol "%abc")   (Just '%') 
test4   = TestCase  $ assertEqual "test4"   (check symbol "&abc")   (Just '&') 
test5   = TestCase  $ assertEqual "test5"   (check symbol "|abc")   (Just '|') 
test6   = TestCase  $ assertEqual "test6"   (check symbol "*abc")   (Just '*') 
test7   = TestCase  $ assertEqual "test7"   (check symbol "+abc")   (Just '+') 
test8   = TestCase  $ assertEqual "test8"   (check symbol "-abc")   (Just '-') 
test9   = TestCase  $ assertEqual "test9"   (check symbol "/abc")   (Just '/') 
test10  = TestCase  $ assertEqual "test10"  (check symbol ":abc")   (Just ':') 
test11  = TestCase  $ assertEqual "test11"  (check symbol "<abc")   (Just '<') 
test12  = TestCase  $ assertEqual "test12"  (check symbol "=abc")   (Just '=') 
test13  = TestCase  $ assertEqual "test13"  (check symbol "?abc")   (Just '?') 
test14  = TestCase  $ assertEqual "test14"  (check symbol ">abc")   (Just '>') 
test15  = TestCase  $ assertEqual "test15"  (check symbol "@abc")   (Just '@') 
test16  = TestCase  $ assertEqual "test16"  (check symbol "^abc")   (Just '^') 
test17  = TestCase  $ assertEqual "test17"  (check symbol "_abc")   (Just '_') 
test18  = TestCase  $ assertEqual "test18"  (check symbol "~abc")   (Just '~') 
test19  = TestCase  $ assertEqual "test19"  (check symbol "#abc")   (Just '#') 
test20  = TestCase  $ assertEqual "test20"  (check symbol "`abc")   (Nothing) 
test21  = TestCase  $ assertEqual "test21"  (check symbol "'abc")   (Nothing) 
test22  = TestCase  $ assertEqual "test22"  (check symbol "\"abc")  (Nothing) 
test23  = TestCase  $ assertEqual "test23"  (check symbol "£abc")   (Nothing) 
test24  = TestCase  $ assertEqual "test24"  (check symbol "(abc")   (Nothing) 
test25  = TestCase  $ assertEqual "test25"  (check symbol ")abc")   (Nothing) 
test26  = TestCase  $ assertEqual "test26"  (check symbol ";abc")   (Nothing) 
test27  = TestCase  $ assertEqual "test27"  (check symbol "\\abc")  (Nothing) 
test28  = TestCase  $ assertEqual "test28"  (check symbol ",abc")   (Nothing) 
test29  = TestCase  $ assertEqual "test29"  (check symbol ".abc")   (Nothing) 
test30  = TestCase  $ assertEqual "test30"  (check symbol "¬abc")   (Nothing) 
test31  = TestCase  $ assertEqual "test31"  (check symbol "aabc")   (Nothing) 
test32  = TestCase  $ assertEqual "test32"  (check symbol "Aabc")   (Nothing) 
test33  = TestCase  $ assertEqual "test33"  (check symbol "0abc")   (Nothing) 
test34  = TestCase  $ assertEqual "test34"  (check symbol "\nabc")  (Nothing) 
test35  = TestCase  $ assertEqual "test35"  (check symbol "\tabc")  (Nothing) 
test36  = TestCase  $ assertEqual "test36"  (check symbol "\rabc")  (Nothing) 
test37  = TestCase  $ assertEqual "test37"  (check symbol "4abc")   (Nothing) 
test38  = TestCase  $ assertEqual "test38"  (check symbol "5abc")   (Nothing) 
test39  = TestCase  $ assertEqual "test39"  (check symbol "6abc")   (Nothing) 
test40  = TestCase  $ assertEqual "test40"  (check symbol "7abc")   (Nothing) 




test_Parse = TestLabel "test_Parse" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  ]

