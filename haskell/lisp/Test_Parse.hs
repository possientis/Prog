module Test_Parse
  ( test_Parse
  ) where


import Text.ParserCombinators.Parsec hiding (spaces)
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
test37  = TestCase  $ assertEqual "test37"  (check symbol "")       (Nothing) 
test38  = TestCase  $ assertEqual "test38"  (check symbol "5abc")   (Nothing) 
test39  = TestCase  $ assertEqual "test39"  (check symbol "6abc")   (Nothing) 
test40  = TestCase  $ assertEqual "test40"  (check symbol "7abc")   (Nothing) 

parser1 = spaces >> char 'a'
test41  = TestCase  $ assertEqual "test41"  (check parser1 "a")     (Nothing) 
test42  = TestCase  $ assertEqual "test42"  (check parser1 " a")    (Just 'a') 
test43  = TestCase  $ assertEqual "test43"  (check parser1 "\ta")   (Just 'a') 
test44  = TestCase  $ assertEqual "test44"  (check parser1 "\ra")   (Just 'a') 
test45  = TestCase  $ assertEqual "test45"  (check parser1 "\na")   (Just 'a') 
test46  = TestCase  $ assertEqual "test45"  (check parser1 "\t a")  (Just 'a') 
test47  = TestCase  $ assertEqual "test45"  (check parser1 "\r\t a")(Just 'a') 
test48  = TestCase  $ assertEqual "test45"  (check parser1 "\n \ta")(Just 'a') 

test49  = TestCase  $ assertEqual "test49"  (check hexChar "axxx")  (Just 'a') 
test50  = TestCase  $ assertEqual "test50"  (check hexChar "bxxx")  (Just 'b') 
test51  = TestCase  $ assertEqual "test51"  (check hexChar "cxxx")  (Just 'c') 
test52  = TestCase  $ assertEqual "test52"  (check hexChar "dxxx")  (Just 'd') 
test53  = TestCase  $ assertEqual "test53"  (check hexChar "exxx")  (Just 'e') 
test54  = TestCase  $ assertEqual "test54"  (check hexChar "fxxx")  (Just 'f') 
test55  = TestCase  $ assertEqual "test55"  (check hexChar "Axxx")  (Just 'A') 
test56  = TestCase  $ assertEqual "test56"  (check hexChar "Bxxx")  (Just 'B') 
test57  = TestCase  $ assertEqual "test57"  (check hexChar "Cxxx")  (Just 'C') 
test58  = TestCase  $ assertEqual "test58"  (check hexChar "Dxxx")  (Just 'D') 
test59  = TestCase  $ assertEqual "test59"  (check hexChar "Exxx")  (Just 'E') 
test60  = TestCase  $ assertEqual "test60"  (check hexChar "Fxxx")  (Just 'F') 
test61  = TestCase  $ assertEqual "test61"  (check hexChar "1xxx")  (Just '1') 
test62  = TestCase  $ assertEqual "test62"  (check hexChar "2xxx")  (Just '2') 
test63  = TestCase  $ assertEqual "test63"  (check hexChar "3xxx")  (Just '3') 
test64  = TestCase  $ assertEqual "test64"  (check hexChar "4xxx")  (Just '4') 
test65  = TestCase  $ assertEqual "test65"  (check hexChar "5xxx")  (Just '5') 
test66  = TestCase  $ assertEqual "test66"  (check hexChar "6xxx")  (Just '6') 
test67  = TestCase  $ assertEqual "test67"  (check hexChar "7xxx")  (Just '7') 
test68  = TestCase  $ assertEqual "test68"  (check hexChar "8xxx")  (Just '8') 
test69  = TestCase  $ assertEqual "test69"  (check hexChar "9xxx")  (Just '9') 
test70  = TestCase  $ assertEqual "test70"  (check hexChar "0xxx")  (Just '0') 
test71  = TestCase  $ assertEqual "test71"  (check hexChar "gxxx")  (Nothing) 
test72  = TestCase  $ assertEqual "test72"  (check hexChar "Gxxx")  (Nothing) 

parser2 = hexNumber
test73  = TestCase  $ assertEqual "test73"  (check parser2 "#x0")   (Just 0) 
test74  = TestCase  $ assertEqual "test74"  (check parser2 "#x1")   (Just 1) 
test75  = TestCase  $ assertEqual "test75"  (check parser2 "#x2")   (Just 2) 
test76  = TestCase  $ assertEqual "test76"  (check parser2 "#xa")   (Just 10) 
test77  = TestCase  $ assertEqual "test77"  (check parser2 "#xb")   (Just 11) 
test78  = TestCase  $ assertEqual "test78"  (check parser2 "#xc")   (Just 12) 
test79  = TestCase  $ assertEqual "test79"  (check parser2 "#xd")   (Just 13) 
test80  = TestCase  $ assertEqual "test80"  (check parser2 "#xe")   (Just 14) 
test81  = TestCase  $ assertEqual "test81"  (check parser2 "#xf")   (Just 15) 
test82  = TestCase  $ assertEqual "test82"  (check parser2 "#xA")   (Just 10) 
test83  = TestCase  $ assertEqual "test83"  (check parser2 "#xB")   (Just 11) 
test84  = TestCase  $ assertEqual "test84"  (check parser2 "#xC")   (Just 12) 
test85  = TestCase  $ assertEqual "test85"  (check parser2 "#xD")   (Just 13) 
test86  = TestCase  $ assertEqual "test86"  (check parser2 "#xE")   (Just 14) 
test87  = TestCase  $ assertEqual "test87"  (check parser2 "#xF")   (Just 15) 
test88  = TestCase  $ assertEqual "test88"  (check parser2 "#xff")  (Just 255) 
test89  = TestCase  $ assertEqual "test89"  (check parser2 "#xEeE") (Just 3822) 
test90  = TestCase  $ assertEqual "test90"  (check parser2 "#xa2e7")(Just 41703) 
test91  = TestCase  $ assertEqual "test91"  (check parser2 "#a2e7") (Nothing) 
test92  = TestCase  $ assertEqual "test92"  (check parser2 "0xff")  (Nothing) 
test93  = TestCase  $ assertEqual "test93"  (check parser2 "#o333") (Nothing) 
test94  = TestCase  $ assertEqual "test94"  (check parser2 "#b1010")(Nothing) 
test95  = TestCase  $ assertEqual "test95"  (check parser2 "x1234") (Nothing) 
test96  = TestCase  $ assertEqual "test96"  (check parser2 "100h")  (Nothing) 









test_Parse = TestLabel "test_Parse" $ TestList
  [ test1,  test2,  test3,  test4,  test5,  test6,  test7,  test8
  , test9,  test10, test11, test12, test13, test14, test15, test16
  , test17, test18, test19, test20, test21, test22, test23, test24
  , test25, test26, test27, test28, test29, test30, test31, test32
  , test33, test34, test35, test36, test37, test38, test39, test40
  , test41, test42, test43, test44, test45, test46, test47, test48
  , test49, test50, test51, test52, test53, test54, test55, test56
  , test57, test58, test59, test60, test61, test62, test63, test64
  , test65, test66, test67, test68, test69, test70, test71, test72
  , test73, test74, test75, test76, test77, test78, test79, test80
  , test81, test82, test83, test84, test85, test86, test87, test88
  , test89, test90, test91, test92, test93, test94, test95, test96
  ]

