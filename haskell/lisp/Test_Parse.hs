module Test_Parse
  ( test_Parse
  ) where


import Text.ParserCombinators.Parsec hiding (spaces)
import Test.HUnit
import Parse
import LispVal

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
test74  = TestCase  $ assertEqual "test74"  (check parser2 "#x1x")  (Just 1) 
test75  = TestCase  $ assertEqual "test75"  (check parser2 "#x2xx") (Just 2) 
test76  = TestCase  $ assertEqual "test76"  (check parser2 "#xaxxx")(Just 10) 
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


test97  = TestCase  $ assertEqual "test97"  (check octChar "0xxx")  (Just '0') 
test98  = TestCase  $ assertEqual "test98"  (check octChar "1xxx")  (Just '1') 
test99  = TestCase  $ assertEqual "test99"  (check octChar "2xxx")  (Just '2') 
test100 = TestCase  $ assertEqual "test100" (check octChar "3xxx")  (Just '3') 
test101 = TestCase  $ assertEqual "test101" (check octChar "4xxx")  (Just '4') 
test102 = TestCase  $ assertEqual "test102" (check octChar "5xxx")  (Just '5') 
test103 = TestCase  $ assertEqual "test103" (check octChar "6xxx")  (Just '6') 
test104 = TestCase  $ assertEqual "test104" (check octChar "7xxx")  (Just '7') 
test105 = TestCase  $ assertEqual "test105" (check octChar "8xxx")  (Nothing) 
test106 = TestCase  $ assertEqual "test106" (check octChar "9xxx")  (Nothing) 
test107 = TestCase  $ assertEqual "test107" (check octChar "axxx")  (Nothing) 
test108 = TestCase  $ assertEqual "test108" (check octChar "Bxxx")  (Nothing) 
test109 = TestCase  $ assertEqual "test109" (check octChar "#xxx")  (Nothing) 
test110 = TestCase  $ assertEqual "test110" (check octChar "xxxx")  (Nothing) 
test111 = TestCase  $ assertEqual "test111" (check octChar "oxxx")  (Nothing) 
test112 = TestCase  $ assertEqual "test112" (check octChar "Oxxx")  (Nothing) 

parser3 = octNumber
test113 = TestCase  $ assertEqual "test113" (check parser3 "#o0")   (Just 0) 
test114 = TestCase  $ assertEqual "test114" (check parser3 "#o1x")  (Just 1) 
test115 = TestCase  $ assertEqual "test115" (check parser3 "#o2xx") (Just 2) 
test116 = TestCase  $ assertEqual "test116" (check parser3 "#o3xxx")(Just 3) 
test117 = TestCase  $ assertEqual "test117" (check parser3 "#o4")   (Just 4) 
test118 = TestCase  $ assertEqual "test118" (check parser3 "#o5")   (Just 5) 
test119 = TestCase  $ assertEqual "test119" (check parser3 "#o6")   (Just 6) 
test120 = TestCase  $ assertEqual "test120" (check parser3 "#o7")   (Just 7) 
test121 = TestCase  $ assertEqual "test121" (check parser3 "#o10")  (Just 8) 
test122 = TestCase  $ assertEqual "test122" (check parser3 "#o11")  (Just 9) 
test123 = TestCase  $ assertEqual "test123" (check parser3 "#o12")  (Just 10) 
test124 = TestCase  $ assertEqual "test124" (check parser3 "#o13")  (Just 11) 
test125 = TestCase  $ assertEqual "test125" (check parser3 "#o14")  (Just 12) 
test126 = TestCase  $ assertEqual "test126" (check parser3 "#o15")  (Just 13) 
test127 = TestCase  $ assertEqual "test127" (check parser3 "#o16")  (Just 14) 
test128 = TestCase  $ assertEqual "test128" (check parser3 "#o17")  (Just 15) 
test129 = TestCase  $ assertEqual "test129" (check parser3 "#o1007")(Just 519) 
test130 = TestCase  $ assertEqual "test130" (check parser3 "#o80")  (Nothing) 
test131 = TestCase  $ assertEqual "test131" (check parser3 "o10")   (Nothing) 
test132 = TestCase  $ assertEqual "test132" (check parser3 "#01")   (Nothing) 
test133 = TestCase  $ assertEqual "test133" (check parser3 "0120")  (Nothing) 
test134 = TestCase  $ assertEqual "test134" (check parser3 "12o")   (Nothing) 
test135 = TestCase  $ assertEqual "test135" (check parser3 "o#11")  (Nothing) 
test136 = TestCase  $ assertEqual "test136" (check parser3 "#oxxx") (Nothing) 

test137 = TestCase  $ assertEqual "test137" (check binChar "0xxx")  (Just '0') 
test138 = TestCase  $ assertEqual "test138" (check binChar "1xxx")  (Just '1') 
test139 = TestCase  $ assertEqual "test139" (check binChar "2xxx")  (Nothing) 
test140 = TestCase  $ assertEqual "test140" (check binChar "3xxx")  (Nothing) 
test141 = TestCase  $ assertEqual "test141" (check binChar "5xxx")  (Nothing) 
test142 = TestCase  $ assertEqual "test142" (check binChar "7xxx")  (Nothing) 
test143 = TestCase  $ assertEqual "test143" (check binChar "axxx")  (Nothing) 
test144 = TestCase  $ assertEqual "test144" (check binChar "Bxxx")  (Nothing) 

parser4 = binNumber
test145 = TestCase  $ assertEqual "test145" (check parser4 "#b0xxx")(Just 0) 
test146 = TestCase  $ assertEqual "test146" (check parser4 "#b1xxx")(Just 1) 
test147 = TestCase  $ assertEqual "test147" (check parser4 "#b10xx")(Just 2) 
test148 = TestCase  $ assertEqual "test148" (check parser4 "#b11xx")(Just 3) 
test149 = TestCase  $ assertEqual "test149" (check parser4 "#b100x")(Just 4) 
test150 = TestCase  $ assertEqual "test150" (check parser4 "#b101x")(Just 5) 
test151 = TestCase  $ assertEqual "test151" (check parser4 "#b110x")(Just 6) 
test152 = TestCase  $ assertEqual "test152" (check parser4 "#b111x")(Just 7) 
test153 = TestCase  $ assertEqual "test153" (check parser4 "#b11110111x")(Just 247) 
test154 = TestCase  $ assertEqual "test154" (check parser4 "#b2xxx")(Nothing) 
test155 = TestCase  $ assertEqual "test155" (check parser4 "#111xx")(Nothing) 
test156 = TestCase  $ assertEqual "test156" (check parser4 "b111xx")(Nothing) 
test157 = TestCase  $ assertEqual "test157" (check parser4 "111bxx")(Nothing) 
test158 = TestCase  $ assertEqual "test158" (check parser4 "b#111x")(Nothing) 
test159 = TestCase  $ assertEqual "test159" (check parser4 "#bxxxx")(Nothing) 
test160 = TestCase  $ assertEqual "test160" (check parser4 "#01xxx")(Nothing) 


parser5 = decNumber
test161 = TestCase  $ assertEqual "test161" (check parser5 "#d0xxx")(Just 0) 
test162 = TestCase  $ assertEqual "test162" (check parser5 "#d34xx")(Just 34) 
test163 = TestCase  $ assertEqual "test163" (check parser5 "#d567x")(Just 567) 
test164 = TestCase  $ assertEqual "test164" (check parser5 "#d4356")(Just 4356) 
test165 = TestCase  $ assertEqual "test165" (check parser5 "0xxxxx")(Just 0) 
test166 = TestCase  $ assertEqual "test166" (check parser5 "1xxxxx")(Just 1) 
test167 = TestCase  $ assertEqual "test167" (check parser5 "2xxxxx")(Just 2) 
test168 = TestCase  $ assertEqual "test168" (check parser5 "45678x")(Just 45678) 
test169 = TestCase  $ assertEqual "test169" (check parser5 "#d0001")(Just 1) 
test170 = TestCase  $ assertEqual "test170" (check parser5 "00023" )(Just 23) 
test171 = TestCase  $ assertEqual "test171" (check parser5 "d12xxx")(Nothing) 
test172 = TestCase  $ assertEqual "test172" (check parser5 "d#23xx")(Nothing) 
test173 = TestCase  $ assertEqual "test173" (check parser5 "x12333")(Nothing) 
test174 = TestCase  $ assertEqual "test174" (check parser5 "")      (Nothing) 
test175 = TestCase  $ assertEqual "test175" (check parser5 "-23300")(Nothing) 
test176 = TestCase  $ assertEqual "test176" (check parser5 "#dxxxx")(Nothing) 


parser6 = parseNumber
num = Just . Number
test177 = TestCase  $ assertEqual "test177" (check parser6 "0xxx")  (num 0) 
test178 = TestCase  $ assertEqual "test178" (check parser6 "#d0x")  (num 0) 
test179 = TestCase  $ assertEqual "test179" (check parser6 "#x0x")  (num 0) 
test180 = TestCase  $ assertEqual "test180" (check parser6 "#o0x")  (num 0) 
test181 = TestCase  $ assertEqual "test181" (check parser6 "#b0x")  (num 0) 
test182 = TestCase  $ assertEqual "test182" (check parser6 "000x")  (num 0) 
test183 = TestCase  $ assertEqual "test183" (check parser6 "#x00")  (num 0) 
test184 = TestCase  $ assertEqual "test184" (check parser6 "#b00")  (num 0) 


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
  , test97, test98, test99, test100,test101,test102,test103,test104
  , test105,test106,test107,test108,test109,test110,test111,test112
  , test113,test114,test115,test116,test117,test118,test119,test120
  , test121,test122,test123,test124,test125,test126,test127,test128
  , test129,test130,test131,test132,test133,test134,test135,test136
  , test137,test138,test139,test140,test141,test142,test143,test144
  , test145,test146,test147,test148,test149,test150,test151,test152
  , test153,test154,test155,test156,test157,test158,test159,test160
  , test161,test162,test163,test164,test165,test166,test167,test168
  , test169,test170,test171,test172,test173,test174,test175,test176
{-  , test177,test178,test179,test180,test181,test182,test183,test184
 -}
  ]

