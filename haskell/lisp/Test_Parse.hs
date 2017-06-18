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

test49  = TestCase  $ assertEqual "test49"  (check hexDigit "axxx")  (Just 'a') 
test50  = TestCase  $ assertEqual "test50"  (check hexDigit "bxxx")  (Just 'b') 
test51  = TestCase  $ assertEqual "test51"  (check hexDigit "cxxx")  (Just 'c') 
test52  = TestCase  $ assertEqual "test52"  (check hexDigit "dxxx")  (Just 'd') 
test53  = TestCase  $ assertEqual "test53"  (check hexDigit "exxx")  (Just 'e') 
test54  = TestCase  $ assertEqual "test54"  (check hexDigit "fxxx")  (Just 'f') 
test55  = TestCase  $ assertEqual "test55"  (check hexDigit "Axxx")  (Just 'A') 
test56  = TestCase  $ assertEqual "test56"  (check hexDigit "Bxxx")  (Just 'B') 
test57  = TestCase  $ assertEqual "test57"  (check hexDigit "Cxxx")  (Just 'C') 
test58  = TestCase  $ assertEqual "test58"  (check hexDigit "Dxxx")  (Just 'D') 
test59  = TestCase  $ assertEqual "test59"  (check hexDigit "Exxx")  (Just 'E') 
test60  = TestCase  $ assertEqual "test60"  (check hexDigit "Fxxx")  (Just 'F') 
test61  = TestCase  $ assertEqual "test61"  (check hexDigit "1xxx")  (Just '1') 
test62  = TestCase  $ assertEqual "test62"  (check hexDigit "2xxx")  (Just '2') 
test63  = TestCase  $ assertEqual "test63"  (check hexDigit "3xxx")  (Just '3') 
test64  = TestCase  $ assertEqual "test64"  (check hexDigit "4xxx")  (Just '4') 
test65  = TestCase  $ assertEqual "test65"  (check hexDigit "5xxx")  (Just '5') 
test66  = TestCase  $ assertEqual "test66"  (check hexDigit "6xxx")  (Just '6') 
test67  = TestCase  $ assertEqual "test67"  (check hexDigit "7xxx")  (Just '7') 
test68  = TestCase  $ assertEqual "test68"  (check hexDigit "8xxx")  (Just '8') 
test69  = TestCase  $ assertEqual "test69"  (check hexDigit "9xxx")  (Just '9') 
test70  = TestCase  $ assertEqual "test70"  (check hexDigit "0xxx")  (Just '0') 
test71  = TestCase  $ assertEqual "test71"  (check hexDigit "gxxx")  (Nothing) 
test72  = TestCase  $ assertEqual "test72"  (check hexDigit "Gxxx")  (Nothing) 

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


test97  = TestCase  $ assertEqual "test97"  (check octDigit "0xxx")  (Just '0') 
test98  = TestCase  $ assertEqual "test98"  (check octDigit "1xxx")  (Just '1') 
test99  = TestCase  $ assertEqual "test99"  (check octDigit "2xxx")  (Just '2') 
test100 = TestCase  $ assertEqual "test100" (check octDigit "3xxx")  (Just '3') 
test101 = TestCase  $ assertEqual "test101" (check octDigit "4xxx")  (Just '4') 
test102 = TestCase  $ assertEqual "test102" (check octDigit "5xxx")  (Just '5') 
test103 = TestCase  $ assertEqual "test103" (check octDigit "6xxx")  (Just '6') 
test104 = TestCase  $ assertEqual "test104" (check octDigit "7xxx")  (Just '7') 
test105 = TestCase  $ assertEqual "test105" (check octDigit "8xxx")  (Nothing) 
test106 = TestCase  $ assertEqual "test106" (check octDigit "9xxx")  (Nothing) 
test107 = TestCase  $ assertEqual "test107" (check octDigit "axxx")  (Nothing) 
test108 = TestCase  $ assertEqual "test108" (check octDigit "Bxxx")  (Nothing) 
test109 = TestCase  $ assertEqual "test109" (check octDigit "#xxx")  (Nothing) 
test110 = TestCase  $ assertEqual "test110" (check octDigit "xxxx")  (Nothing) 
test111 = TestCase  $ assertEqual "test111" (check octDigit "oxxx")  (Nothing) 
test112 = TestCase  $ assertEqual "test112" (check octDigit "Oxxx")  (Nothing) 

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

test137 = TestCase  $ assertEqual "test137" (check binDigit "0xxx")  (Just '0') 
test138 = TestCase  $ assertEqual "test138" (check binDigit "1xxx")  (Just '1') 
test139 = TestCase  $ assertEqual "test139" (check binDigit "2xxx")  (Nothing) 
test140 = TestCase  $ assertEqual "test140" (check binDigit "3xxx")  (Nothing) 
test141 = TestCase  $ assertEqual "test141" (check binDigit "5xxx")  (Nothing) 
test142 = TestCase  $ assertEqual "test142" (check binDigit "7xxx")  (Nothing) 
test143 = TestCase  $ assertEqual "test143" (check binDigit "axxx")  (Nothing) 
test144 = TestCase  $ assertEqual "test144" (check binDigit "Bxxx")  (Nothing) 

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
test165 = TestCase  $ assertEqual "test165" (check parser5 "#d0xxx")(Just 0) 
test166 = TestCase  $ assertEqual "test166" (check parser5 "#d1xxx")(Just 1) 
test167 = TestCase  $ assertEqual "test167" (check parser5 "#d2xxx")(Just 2) 
test168 = TestCase  $ assertEqual "test168" (check parser5 "#d4567")(Just 4567) 
test169 = TestCase  $ assertEqual "test169" (check parser5 "#d0001")(Just 1) 
test170 = TestCase  $ assertEqual "test170" (check parser5 "#d023" )(Just 23) 
test171 = TestCase  $ assertEqual "test171" (check parser5 "d12xxx")(Nothing) 
test172 = TestCase  $ assertEqual "test172" (check parser5 "d#23xx")(Nothing) 
test173 = TestCase  $ assertEqual "test173" (check parser5 "x12333")(Nothing) 
test174 = TestCase  $ assertEqual "test174" (check parser5 "")      (Nothing) 
test175 = TestCase  $ assertEqual "test175" (check parser5 "-23300")(Nothing) 
test176 = TestCase  $ assertEqual "test176" (check parser5 "#dxxxx")(Nothing) 


parser6 = parseNumber
num = Just . Number
test177 = TestCase  $ assertEqual "test177" (check parser6 "0xxxx") (num 0) 
test178 = TestCase  $ assertEqual "test178" (check parser6 "#o0xx") (num 0) 
test179 = TestCase  $ assertEqual "test179" (check parser6 "#d0xx") (num 0) 
test180 = TestCase  $ assertEqual "test180" (check parser6 "#d00x") (num 0) 
test181 = TestCase  $ assertEqual "test181" (check parser6 "#b0xx") (num 0) 
test182 = TestCase  $ assertEqual "test182" (check parser6 "#b00x") (num 0) 
test183 = TestCase  $ assertEqual "test183" (check parser6 "#x0xx") (num 0) 
test184 = TestCase  $ assertEqual "test184" (check parser6 "#x00x") (num 0) 

test185 = TestCase  $ assertEqual "test185" (check parser6 "1xxxx") (num 1) 
test186 = TestCase  $ assertEqual "test186" (check parser6 "#o1xx") (num 1) 
test187 = TestCase  $ assertEqual "test187" (check parser6 "#d1xx") (num 1) 
test188 = TestCase  $ assertEqual "test188" (check parser6 "#d01x") (num 1) 
test189 = TestCase  $ assertEqual "test189" (check parser6 "#b1xx") (num 1) 
test190 = TestCase  $ assertEqual "test190" (check parser6 "#b01x") (num 1) 
test191 = TestCase  $ assertEqual "test191" (check parser6 "#x1xx") (num 1) 
test192 = TestCase  $ assertEqual "test192" (check parser6 "#x01x") (num 1) 

test193 = TestCase  $ assertEqual "test193" (check parser6 "2xxxx") (num 2) 
test194 = TestCase  $ assertEqual "test194" (check parser6 "#o2xx") (num 2) 
test195 = TestCase  $ assertEqual "test195" (check parser6 "#d2xx") (num 2) 
test196 = TestCase  $ assertEqual "test196" (check parser6 "#d02x") (num 2) 
test197 = TestCase  $ assertEqual "test197" (check parser6 "#b10x") (num 2) 
test198 = TestCase  $ assertEqual "test198" (check parser6 "#b010") (num 2) 
test199 = TestCase  $ assertEqual "test199" (check parser6 "#x2xx") (num 2) 
test200 = TestCase  $ assertEqual "test200" (check parser6 "#x02x") (num 2) 

test201 = TestCase  $ assertEqual "test201" (check parser6 "3xxxx") (num 3) 
test202 = TestCase  $ assertEqual "test202" (check parser6 "#o3xx") (num 3) 
test203 = TestCase  $ assertEqual "test203" (check parser6 "#d3xx") (num 3) 
test204 = TestCase  $ assertEqual "test204" (check parser6 "#d03x") (num 3) 
test205 = TestCase  $ assertEqual "test205" (check parser6 "#b11x") (num 3) 
test206 = TestCase  $ assertEqual "test206" (check parser6 "#b011") (num 3) 
test207 = TestCase  $ assertEqual "test207" (check parser6 "#x3xx") (num 3) 
test208 = TestCase  $ assertEqual "test208" (check parser6 "#x03x") (num 3) 

test209 = TestCase  $ assertEqual "test209" (check parser6 "4xxxx") (num 4) 
test210 = TestCase  $ assertEqual "test210" (check parser6 "#o4xx") (num 4) 
test211 = TestCase  $ assertEqual "test211" (check parser6 "#d4xx") (num 4) 
test212 = TestCase  $ assertEqual "test212" (check parser6 "#d04x") (num 4) 
test213 = TestCase  $ assertEqual "test213" (check parser6 "#b100") (num 4) 
test214 = TestCase  $ assertEqual "test214" (check parser6 "#b0100")(num 4) 
test215 = TestCase  $ assertEqual "test215" (check parser6 "#x4xx") (num 4) 
test216 = TestCase  $ assertEqual "test216" (check parser6 "#x04x") (num 4) 

test217 = TestCase  $ assertEqual "test217" (check parser6 "5xxxx") (num 5) 
test218 = TestCase  $ assertEqual "test218" (check parser6 "#o5xx") (num 5) 
test219 = TestCase  $ assertEqual "test219" (check parser6 "#d5xx") (num 5) 
test220 = TestCase  $ assertEqual "test220" (check parser6 "#d05x") (num 5) 
test221 = TestCase  $ assertEqual "test221" (check parser6 "#b101") (num 5) 
test222 = TestCase  $ assertEqual "test222" (check parser6 "#b0101")(num 5) 
test223 = TestCase  $ assertEqual "test223" (check parser6 "#x5xx") (num 5) 
test224 = TestCase  $ assertEqual "test224" (check parser6 "#x05x") (num 5) 

test225 = TestCase  $ assertEqual "test225" (check parser6 "6xxxx") (num 6) 
test226 = TestCase  $ assertEqual "test226" (check parser6 "#o6x")  (num 6) 
test227 = TestCase  $ assertEqual "test227" (check parser6 "#d6xx") (num 6) 
test228 = TestCase  $ assertEqual "test228" (check parser6 "#d06x") (num 6) 
test229 = TestCase  $ assertEqual "test229" (check parser6 "#b110") (num 6) 
test230 = TestCase  $ assertEqual "test230" (check parser6 "#b0110")(num 6) 
test231 = TestCase  $ assertEqual "test231" (check parser6 "#x6xx") (num 6) 
test232 = TestCase  $ assertEqual "test232" (check parser6 "#x06x") (num 6) 

test233 = TestCase  $ assertEqual "test233" (check parser6 "7xxxx") (num 7) 
test234 = TestCase  $ assertEqual "test234" (check parser6 "#o7x")  (num 7) 
test235 = TestCase  $ assertEqual "test235" (check parser6 "#d7xx") (num 7) 
test236 = TestCase  $ assertEqual "test236" (check parser6 "#d07x") (num 7) 
test237 = TestCase  $ assertEqual "test237" (check parser6 "#b111") (num 7) 
test238 = TestCase  $ assertEqual "test238" (check parser6 "#b0111")(num 7) 
test239 = TestCase  $ assertEqual "test239" (check parser6 "#x7xx") (num 7) 
test240 = TestCase  $ assertEqual "test240" (check parser6 "#x07x") (num 7) 

test241 = TestCase  $ assertEqual "test241" (check parser6 "8xxxx")   (num 8) 
test242 = TestCase  $ assertEqual "test242" (check parser6 "#o10x")   (num 8) 
test243 = TestCase  $ assertEqual "test243" (check parser6 "#d8xx")   (num 8) 
test244 = TestCase  $ assertEqual "test244" (check parser6 "#d08x")   (num 8) 
test245 = TestCase  $ assertEqual "test245" (check parser6 "#b1000")  (num 8) 
test246 = TestCase  $ assertEqual "test246" (check parser6 "#b01000") (num 8) 
test247 = TestCase  $ assertEqual "test247" (check parser6 "#x8xx")   (num 8) 
test248 = TestCase  $ assertEqual "test248" (check parser6 "#x08x")   (num 8) 

test249 = TestCase  $ assertEqual "test249" (check parser6 "9xxxx")   (num 9) 
test250 = TestCase  $ assertEqual "test250" (check parser6 "#o11x")   (num 9) 
test251 = TestCase  $ assertEqual "test251" (check parser6 "#d9xx")   (num 9) 
test252 = TestCase  $ assertEqual "test252" (check parser6 "#d09x")   (num 9) 
test253 = TestCase  $ assertEqual "test253" (check parser6 "#b1001")  (num 9) 
test254 = TestCase  $ assertEqual "test254" (check parser6 "#b01001") (num 9) 
test255 = TestCase  $ assertEqual "test255" (check parser6 "#x9xx")   (num 9) 
test256 = TestCase  $ assertEqual "test256" (check parser6 "#x09x")   (num 9) 

test257 = TestCase  $ assertEqual "test257" (check parser6 "10xxx")   (num 10) 
test258 = TestCase  $ assertEqual "test258" (check parser6 "#o12x")   (num 10) 
test259 = TestCase  $ assertEqual "test259" (check parser6 "#d10x")   (num 10) 
test260 = TestCase  $ assertEqual "test260" (check parser6 "#d010x")  (num 10) 
test261 = TestCase  $ assertEqual "test261" (check parser6 "#b1010")  (num 10) 
test262 = TestCase  $ assertEqual "test262" (check parser6 "#b01010") (num 10) 
test263 = TestCase  $ assertEqual "test263" (check parser6 "#xaxx")   (num 10) 
test264 = TestCase  $ assertEqual "test264" (check parser6 "#x0Ax")   (num 10) 

test265 = TestCase  $ assertEqual "test265" (check parser6 "11xxx")   (num 11) 
test266 = TestCase  $ assertEqual "test266" (check parser6 "#o13x")   (num 11) 
test267 = TestCase  $ assertEqual "test267" (check parser6 "#d11x")   (num 11) 
test268 = TestCase  $ assertEqual "test268" (check parser6 "#d011x")  (num 11) 
test269 = TestCase  $ assertEqual "test269" (check parser6 "#b1011")  (num 11) 
test270 = TestCase  $ assertEqual "test270" (check parser6 "#b01011") (num 11) 
test271 = TestCase  $ assertEqual "test271" (check parser6 "#xbxx")   (num 11) 
test272 = TestCase  $ assertEqual "test272" (check parser6 "#x0Bx")   (num 11) 

test273 = TestCase  $ assertEqual "test273" (check parser6 "12xxx")   (num 12) 
test274 = TestCase  $ assertEqual "test274" (check parser6 "#o14x")   (num 12) 
test275 = TestCase  $ assertEqual "test275" (check parser6 "#d12x")   (num 12) 
test276 = TestCase  $ assertEqual "test276" (check parser6 "#d012x")  (num 12) 
test277 = TestCase  $ assertEqual "test277" (check parser6 "#b1100")  (num 12) 
test278 = TestCase  $ assertEqual "test278" (check parser6 "#b01100") (num 12) 
test279 = TestCase  $ assertEqual "test279" (check parser6 "#xCxx")   (num 12) 
test280 = TestCase  $ assertEqual "test280" (check parser6 "#x0cx")   (num 12) 

test281 = TestCase  $ assertEqual "test281" (check parser6 "13xxx")   (num 13) 
test282 = TestCase  $ assertEqual "test282" (check parser6 "#o15x")   (num 13) 
test283 = TestCase  $ assertEqual "test283" (check parser6 "#d13x")   (num 13) 
test284 = TestCase  $ assertEqual "test284" (check parser6 "#d013x")  (num 13) 
test285 = TestCase  $ assertEqual "test285" (check parser6 "#b1101")  (num 13) 
test286 = TestCase  $ assertEqual "test286" (check parser6 "#b01101") (num 13) 
test287 = TestCase  $ assertEqual "test287" (check parser6 "#xDxx")   (num 13) 
test288 = TestCase  $ assertEqual "test288" (check parser6 "#x0dx")   (num 13) 

test289 = TestCase  $ assertEqual "test289" (check parser6 "14xxx")   (num 14) 
test290 = TestCase  $ assertEqual "test290" (check parser6 "#o16x")   (num 14) 
test291 = TestCase  $ assertEqual "test291" (check parser6 "#d14x")   (num 14) 
test292 = TestCase  $ assertEqual "test292" (check parser6 "#d014x")  (num 14) 
test293 = TestCase  $ assertEqual "test293" (check parser6 "#b1110")  (num 14) 
test294 = TestCase  $ assertEqual "test294" (check parser6 "#b01110") (num 14) 
test295 = TestCase  $ assertEqual "test295" (check parser6 "#xexx")   (num 14) 
test296 = TestCase  $ assertEqual "test296" (check parser6 "#x0Ex")   (num 14) 

test297 = TestCase  $ assertEqual "test297" (check parser6 "15xxx")   (num 15) 
test298 = TestCase  $ assertEqual "test298" (check parser6 "#o17x")   (num 15) 
test299 = TestCase  $ assertEqual "test299" (check parser6 "#d15x")   (num 15) 
test300 = TestCase  $ assertEqual "test300" (check parser6 "#d015x")  (num 15) 
test301 = TestCase  $ assertEqual "test301" (check parser6 "#b1111")  (num 15) 
test302 = TestCase  $ assertEqual "test302" (check parser6 "#b01111") (num 15) 
test303 = TestCase  $ assertEqual "test303" (check parser6 "#xfxx")   (num 15) 
test304 = TestCase  $ assertEqual "test304" (check parser6 "#x0Fx")   (num 15) 

test305 = TestCase  $ assertEqual "test305" (check parser6 "16xxx")   (num 16) 
test306 = TestCase  $ assertEqual "test306" (check parser6 "#o20x")   (num 16) 
test307 = TestCase  $ assertEqual "test307" (check parser6 "#d16x")   (num 16) 
test308 = TestCase  $ assertEqual "test308" (check parser6 "#d016x")  (num 16) 
test309 = TestCase  $ assertEqual "test309" (check parser6 "#b10000") (num 16) 
test310 = TestCase  $ assertEqual "test310" (check parser6 "#b010000")(num 16) 
test311 = TestCase  $ assertEqual "test311" (check parser6 "#x10xx")  (num 16) 
test312 = TestCase  $ assertEqual "test312" (check parser6 "#x010x")  (num 16) 


test313 = TestCase  $ assertEqual "test313" (check parser6 "29xxx")   (num 29) 
test314 = TestCase  $ assertEqual "test314" (check parser6 "#o35x")   (num 29) 
test315 = TestCase  $ assertEqual "test315" (check parser6 "#d29x")   (num 29) 
test316 = TestCase  $ assertEqual "test316" (check parser6 "#d029x")  (num 29) 
test317 = TestCase  $ assertEqual "test317" (check parser6 "#b11101") (num 29) 
test318 = TestCase  $ assertEqual "test318" (check parser6 "#b011101")(num 29) 
test319 = TestCase  $ assertEqual "test319" (check parser6 "#x1dxx")  (num 29) 
test320 = TestCase  $ assertEqual "test320" (check parser6 "#x01dx")  (num 29) 

binStr1 = "#b10100110110110101xxxx"
binStr2 = "#b00010100110110110101xxxx"
test321 = TestCase  $ assertEqual "test321" (check parser6 "85429xxx")(num 85429) 
test322 = TestCase  $ assertEqual "test322" (check parser6 "#o246665")(num 85429) 
test323 = TestCase  $ assertEqual "test323" (check parser6 "#d85429x")(num 85429) 
test324 = TestCase  $ assertEqual "test324" (check parser6 "#d085429")(num 85429) 
test325 = TestCase  $ assertEqual "test325" (check parser6 binStr1)   (num 85429) 
test326 = TestCase  $ assertEqual "test326" (check parser6 binStr2)   (num 85429) 
test327 = TestCase  $ assertEqual "test327" (check parser6 "#x14db5x")(num 85429) 
test328 = TestCase  $ assertEqual "test328" (check parser6 "#x014db5")(num 85429) 


parser7 = parseChar
ch = Just . Char
test329 = TestCase  $ assertEqual "test329" (check parser7 "#\\axxxx")(ch 'a') 
test330 = TestCase  $ assertEqual "test330" (check parser7 "#\\bxxxx")(ch 'b') 
test331 = TestCase  $ assertEqual "test331" (check parser7 "#\\cxxxx")(ch 'c') 
test332 = TestCase  $ assertEqual "test332" (check parser7 "#\\dxxxx")(ch 'd') 
test333 = TestCase  $ assertEqual "test333" (check parser7 "#\\exxxx")(ch 'e') 
test334 = TestCase  $ assertEqual "test334" (check parser7 "#\\fxxxx")(ch 'f') 
test335 = TestCase  $ assertEqual "test335" (check parser7 "#\\gxxxx")(ch 'g') 
test336 = TestCase  $ assertEqual "test336" (check parser7 "#\\hxxxx")(ch 'h') 
test337 = TestCase  $ assertEqual "test337" (check parser7 "#\\ixxxx")(ch 'i') 
test338 = TestCase  $ assertEqual "test338" (check parser7 "#\\jxxxx")(ch 'j') 
test339 = TestCase  $ assertEqual "test339" (check parser7 "#\\kxxxx")(ch 'k') 
test340 = TestCase  $ assertEqual "test340" (check parser7 "#\\lxxxx")(ch 'l') 
test341 = TestCase  $ assertEqual "test341" (check parser7 "#\\mxxxx")(ch 'm') 
test342 = TestCase  $ assertEqual "test342" (check parser7 "#\\nxxxx")(ch 'n') 
test343 = TestCase  $ assertEqual "test343" (check parser7 "#\\oxxxx")(ch 'o') 
test344 = TestCase  $ assertEqual "test344" (check parser7 "#\\pxxxx")(ch 'p') 
test345 = TestCase  $ assertEqual "test345" (check parser7 "#\\qxxxx")(ch 'q') 
test346 = TestCase  $ assertEqual "test346" (check parser7 "#\\rxxxx")(ch 'r') 
test347 = TestCase  $ assertEqual "test347" (check parser7 "#\\sxxxx")(ch 's') 
test348 = TestCase  $ assertEqual "test348" (check parser7 "#\\txxxx")(ch 't') 
test349 = TestCase  $ assertEqual "test349" (check parser7 "#\\uxxxx")(ch 'u') 
test350 = TestCase  $ assertEqual "test350" (check parser7 "#\\vxxxx")(ch 'v') 
test351 = TestCase  $ assertEqual "test351" (check parser7 "#\\wxxxx")(ch 'w') 
test352 = TestCase  $ assertEqual "test352" (check parser7 "#\\xxxxx")(ch 'x') 
test353 = TestCase  $ assertEqual "test353" (check parser7 "#\\yxxxx")(ch 'y') 
test354 = TestCase  $ assertEqual "test354" (check parser7 "#\\zxxxx")(ch 'z') 
test355 = TestCase  $ assertEqual "test355" (check parser7 "#\\Axxxx")(ch 'A') 
test356 = TestCase  $ assertEqual "test356" (check parser7 "#\\Bxxxx")(ch 'B') 
test357 = TestCase  $ assertEqual "test357" (check parser7 "#\\Cxxxx")(ch 'C') 
test358 = TestCase  $ assertEqual "test358" (check parser7 "#\\Dxxxx")(ch 'D') 
test359 = TestCase  $ assertEqual "test359" (check parser7 "#\\Exxxx")(ch 'E') 
test360 = TestCase  $ assertEqual "test360" (check parser7 "#\\Fxxxx")(ch 'F') 
test361 = TestCase  $ assertEqual "test361" (check parser7 "#\\Gxxxx")(ch 'G') 
test362 = TestCase  $ assertEqual "test362" (check parser7 "#\\Hxxxx")(ch 'H') 
test363 = TestCase  $ assertEqual "test363" (check parser7 "#\\Ixxxx")(ch 'I') 
test364 = TestCase  $ assertEqual "test364" (check parser7 "#\\Jxxxx")(ch 'J') 
test365 = TestCase  $ assertEqual "test365" (check parser7 "#\\Kxxxx")(ch 'K') 
test366 = TestCase  $ assertEqual "test366" (check parser7 "#\\Lxxxx")(ch 'L') 
test367 = TestCase  $ assertEqual "test367" (check parser7 "#\\Mxxxx")(ch 'M') 
test368 = TestCase  $ assertEqual "test368" (check parser7 "#\\Nxxxx")(ch 'N') 
test369 = TestCase  $ assertEqual "test369" (check parser7 "#\\Oxxxx")(ch 'O') 
test370 = TestCase  $ assertEqual "test370" (check parser7 "#\\Pxxxx")(ch 'P') 
test371 = TestCase  $ assertEqual "test371" (check parser7 "#\\Qxxxx")(ch 'Q') 
test372 = TestCase  $ assertEqual "test372" (check parser7 "#\\Rxxxx")(ch 'R') 
test373 = TestCase  $ assertEqual "test373" (check parser7 "#\\Sxxxx")(ch 'S') 
test374 = TestCase  $ assertEqual "test374" (check parser7 "#\\Txxxx")(ch 'T') 
test375 = TestCase  $ assertEqual "test375" (check parser7 "#\\Uxxxx")(ch 'U') 
test376 = TestCase  $ assertEqual "test376" (check parser7 "#\\Vxxxx")(ch 'V') 
test377 = TestCase  $ assertEqual "test377" (check parser7 "#\\Wxxxx")(ch 'W') 
test378 = TestCase  $ assertEqual "test378" (check parser7 "#\\Xxxxx")(ch 'X') 
test379 = TestCase  $ assertEqual "test379" (check parser7 "#\\Yxxxx")(ch 'Y') 
test380 = TestCase  $ assertEqual "test380" (check parser7 "#\\Zxxxx")(ch 'Z') 
test381 = TestCase  $ assertEqual "test381" (check parser7 "#\\0xxxx")(ch '0') 
test382 = TestCase  $ assertEqual "test382" (check parser7 "#\\1xxxx")(ch '1') 
test383 = TestCase  $ assertEqual "test383" (check parser7 "#\\2xxxx")(ch '2') 
test384 = TestCase  $ assertEqual "test384" (check parser7 "#\\3xxxx")(ch '3') 
test385 = TestCase  $ assertEqual "test385" (check parser7 "#\\4xxxx")(ch '4') 
test386 = TestCase  $ assertEqual "test386" (check parser7 "#\\5xxxx")(ch '5') 
test387 = TestCase  $ assertEqual "test387" (check parser7 "#\\6xxxx")(ch '6') 
test388 = TestCase  $ assertEqual "test388" (check parser7 "#\\7xxxx")(ch '7') 
test389 = TestCase  $ assertEqual "test389" (check parser7 "#\\8xxxx")(ch '8') 
test390 = TestCase  $ assertEqual "test390" (check parser7 "#\\9xxxx")(ch '9') 
test391 = TestCase  $ assertEqual "test391" (check parser7 "#\\!xxxx")(ch '!') 
test392 = TestCase  $ assertEqual "test392" (check parser7 "#\\$xxxx")(ch '$') 

test393 = TestCase  $ assertEqual "test393" (check parser7 "#\\%xxxx")(ch '%') 
test394 = TestCase  $ assertEqual "test394" (check parser7 "#\\&xxxx")(ch '&') 
test395 = TestCase  $ assertEqual "test395" (check parser7 "#\\|xxxx")(ch '|') 
test396 = TestCase  $ assertEqual "test396" (check parser7 "#\\*xxxx")(ch '*') 
test397 = TestCase  $ assertEqual "test397" (check parser7 "#\\+xxxx")(ch '+') 
test398 = TestCase  $ assertEqual "test398" (check parser7 "#\\-xxxx")(ch '-') 
test399 = TestCase  $ assertEqual "test399" (check parser7 "#\\/xxxx")(ch '/') 
test400 = TestCase  $ assertEqual "test400" (check parser7 "#\\:xxxx")(ch ':') 

test401 = TestCase  $ assertEqual "test401" (check parser7 "#\\<xxxx")(ch '<') 
test402 = TestCase  $ assertEqual "test402" (check parser7 "#\\=xxxx")(ch '=') 
test403 = TestCase  $ assertEqual "test403" (check parser7 "#\\?xxxx")(ch '?') 
test404 = TestCase  $ assertEqual "test404" (check parser7 "#\\>xxxx")(ch '>') 
test405 = TestCase  $ assertEqual "test405" (check parser7 "#\\@xxxx")(ch '@') 
test406 = TestCase  $ assertEqual "test406" (check parser7 "#\\^xxxx")(ch '^') 
test407 = TestCase  $ assertEqual "test407" (check parser7 "#\\_xxxx")(ch '_') 
test408 = TestCase  $ assertEqual "test408" (check parser7 "#\\~xxxx")(ch '~') 

test409 = TestCase  $ assertEqual "test409" (check parser7 "#\\`xxxx")(ch '`') 
test410 = TestCase  $ assertEqual "test410" (check parser7 "#\\'xxxx")(ch '\'') 
test411 = TestCase  $ assertEqual "test411" (check parser7 "#\\\"xxx")(ch '"') 
test412 = TestCase  $ assertEqual "test412" (check parser7 "#\\(xxxx")(ch '(') 
test413 = TestCase  $ assertEqual "test413" (check parser7 "#\\)xxxx")(ch ')') 
test414 = TestCase  $ assertEqual "test414" (check parser7 "#\\;xxxx")(ch ';') 
test415 = TestCase  $ assertEqual "test415" (check parser7 "#\\\\xxx")(ch '\\') 
test416 = TestCase  $ assertEqual "test416" (check parser7 "#\\,xxxx")(ch ',') 

test417 = TestCase  $ assertEqual "test417" (check parser7 "#\\.xxxx")(ch '.') 
test418 = TestCase  $ assertEqual "test418" (check parser7 "#\\£xxxx")(Nothing) 
test419 = TestCase  $ assertEqual "test419" (check parser7 "#\\¬xxxx")(Nothing) 
test420 = TestCase  $ assertEqual "test420" (check parser7 "\\axxxxx")(Nothing) 
test421 = TestCase  $ assertEqual "test421" (check parser7 "#axxxxxx")(Nothing) 
test422 = TestCase  $ assertEqual "test422" (check parser7 "\\#axxxx")(Nothing) 
test423 = TestCase  $ assertEqual "test423" (check parser7 "\'a\'xxx")(Nothing) 
test424 = TestCase  $ assertEqual "test424" (check parser7 "\"a\"xxx")(Nothing) 

test425 = TestCase  $ assertEqual "test425" (check parser7 "#\\000xx")(ch '\NUL') 
test426 = TestCase  $ assertEqual "test426" (check parser7 "#\\001xx")(ch '\SOH') 
test427 = TestCase  $ assertEqual "test427" (check parser7 "#\\002xx")(ch '\STX') 
test428 = TestCase  $ assertEqual "test428" (check parser7 "#\\003xx")(ch '\ETX') 
test429 = TestCase  $ assertEqual "test429" (check parser7 "#\\004xx")(ch '\EOT') 
test430 = TestCase  $ assertEqual "test430" (check parser7 "#\\005xx")(ch '\ENQ') 
test431 = TestCase  $ assertEqual "test431" (check parser7 "#\\006xx")(ch '\ACK') 
test432 = TestCase  $ assertEqual "test432" (check parser7 "#\\007xx")(ch '\BEL') 

test433 = TestCase  $ assertEqual "test433" (check parser7 "#\\010xx")(ch '\BS') 
test434 = TestCase  $ assertEqual "test434" (check parser7 "#\\011xx")(ch '\HT') 
test435 = TestCase  $ assertEqual "test435" (check parser7 "#\\012xx")(ch '\LF') 
test436 = TestCase  $ assertEqual "test436" (check parser7 "#\\013xx")(ch '\VT') 
test437 = TestCase  $ assertEqual "test437" (check parser7 "#\\014xx")(ch '\FF') 
test438 = TestCase  $ assertEqual "test438" (check parser7 "#\\015xx")(ch '\CR') 
test439 = TestCase  $ assertEqual "test439" (check parser7 "#\\016xx")(ch '\SO') 
test440 = TestCase  $ assertEqual "test440" (check parser7 "#\\017xx")(ch '\SI') 

test441 = TestCase  $ assertEqual "test441" (check parser7 "#\\020xx")(ch '\DLE') 
test442 = TestCase  $ assertEqual "test442" (check parser7 "#\\021xx")(ch '\DC1') 
test443 = TestCase  $ assertEqual "test443" (check parser7 "#\\022xx")(ch '\DC2') 
test444 = TestCase  $ assertEqual "test444" (check parser7 "#\\023xx")(ch '\DC3') 
test445 = TestCase  $ assertEqual "test445" (check parser7 "#\\024xx")(ch '\DC4') 
test446 = TestCase  $ assertEqual "test446" (check parser7 "#\\025xx")(ch '\NAK') 
test447 = TestCase  $ assertEqual "test447" (check parser7 "#\\026xx")(ch '\SYN') 
test448 = TestCase  $ assertEqual "test448" (check parser7 "#\\027xx")(ch '\ETB') 

test449 = TestCase  $ assertEqual "test449" (check parser7 "#\\030xx")(ch '\CAN') 
test450 = TestCase  $ assertEqual "test450" (check parser7 "#\\031xx")(ch '\EM') 
test451 = TestCase  $ assertEqual "test451" (check parser7 "#\\032xx")(ch '\SUB') 
test452 = TestCase  $ assertEqual "test452" (check parser7 "#\\033xx")(ch '\ESC') 
test453 = TestCase  $ assertEqual "test453" (check parser7 "#\\034xx")(ch '\FS') 
test454 = TestCase  $ assertEqual "test454" (check parser7 "#\\035xx")(ch '\GS') 
test455 = TestCase  $ assertEqual "test455" (check parser7 "#\\036xx")(ch '\RS') 
test456 = TestCase  $ assertEqual "test456" (check parser7 "#\\037xx")(ch '\US') 

test457 = TestCase  $ assertEqual "test457" (check parser7 "#\\040xx")(ch '\SP') 
test458 = TestCase  $ assertEqual "test458" (check parser7 "#\\177xx")(ch '\DEL') 
test459 = TestCase  $ assertEqual "test459" (check parser7 "#\\40xxx")(ch '\SP') 
test460 = TestCase  $ assertEqual "test460" (check parser7 "#\\0040x")(ch '\SP') 
test461 = TestCase  $ assertEqual "test461" (check parser7 "#40xxxxx")(Nothing) 
test462 = TestCase  $ assertEqual "test462" (check parser7 "\\40xxxx")(Nothing) 
test463 = TestCase  $ assertEqual "test463" (check parser7 "\\#40xxx")(Nothing) 
test464 = TestCase  $ assertEqual "test464" (check parser7 "\\o40xxx")(Nothing) 

test465 = TestCase  $ assertEqual "test465" (check parser7 "#\\141xx")(ch 'a') 
test466 = TestCase  $ assertEqual "test466" (check parser7 "#\\142xx")(ch 'b') 
test467 = TestCase  $ assertEqual "test467" (check parser7 "#\\143xx")(ch 'c') 
test468 = TestCase  $ assertEqual "test468" (check parser7 "#\\144xx")(ch 'd') 
test469 = TestCase  $ assertEqual "test469" (check parser7 "#\\145xx")(ch 'e') 
test470 = TestCase  $ assertEqual "test470" (check parser7 "#\\146xx")(ch 'f') 
test471 = TestCase  $ assertEqual "test471" (check parser7 "#\\147xx")(ch 'g') 
test472 = TestCase  $ assertEqual "test472" (check parser7 "#\\150xx")(ch 'h') 
-- TODO
test473 = TestCase  $ assertEqual "test473" (check parser7 "#\\ixxxx")(ch 'i') 
test474 = TestCase  $ assertEqual "test474" (check parser7 "#\\jxxxx")(ch 'j') 
test475 = TestCase  $ assertEqual "test475" (check parser7 "#\\kxxxx")(ch 'k') 
test476 = TestCase  $ assertEqual "test476" (check parser7 "#\\lxxxx")(ch 'l') 
test477 = TestCase  $ assertEqual "test477" (check parser7 "#\\mxxxx")(ch 'm') 
test478 = TestCase  $ assertEqual "test478" (check parser7 "#\\nxxxx")(ch 'n') 
test479 = TestCase  $ assertEqual "test479" (check parser7 "#\\oxxxx")(ch 'o') 
test480 = TestCase  $ assertEqual "test480" (check parser7 "#\\pxxxx")(ch 'p') 

test481 = TestCase  $ assertEqual "test481" (check parser7 "#\\qxxxx")(ch 'q') 
test482 = TestCase  $ assertEqual "test482" (check parser7 "#\\rxxxx")(ch 'r') 
test483 = TestCase  $ assertEqual "test483" (check parser7 "#\\sxxxx")(ch 's') 
test484 = TestCase  $ assertEqual "test484" (check parser7 "#\\txxxx")(ch 't') 
test485 = TestCase  $ assertEqual "test485" (check parser7 "#\\uxxxx")(ch 'u') 
test486 = TestCase  $ assertEqual "test486" (check parser7 "#\\vxxxx")(ch 'v') 
test487 = TestCase  $ assertEqual "test487" (check parser7 "#\\wxxxx")(ch 'w') 
test488 = TestCase  $ assertEqual "test488" (check parser7 "#\\xxxxx")(ch 'x') 

test489 = TestCase  $ assertEqual "test489" (check parser7 "#\\yxxxx")(ch 'y') 
test490 = TestCase  $ assertEqual "test490" (check parser7 "#\\zxxxx")(ch 'z') 
test491 = TestCase  $ assertEqual "test491" (check parser7 "#\\Axxxx")(ch 'A') 
test492 = TestCase  $ assertEqual "test492" (check parser7 "#\\Bxxxx")(ch 'B') 
test493 = TestCase  $ assertEqual "test493" (check parser7 "#\\Cxxxx")(ch 'C') 
test494 = TestCase  $ assertEqual "test494" (check parser7 "#\\Dxxxx")(ch 'D') 
test495 = TestCase  $ assertEqual "test495" (check parser7 "#\\Exxxx")(ch 'E') 
test496 = TestCase  $ assertEqual "test496" (check parser7 "#\\Fxxxx")(ch 'F') 

test497 = TestCase  $ assertEqual "test497" (check parser7 "#\\Gxxxx")(ch 'G') 
test498 = TestCase  $ assertEqual "test498" (check parser7 "#\\Hxxxx")(ch 'H') 
test499 = TestCase  $ assertEqual "test499" (check parser7 "#\\Ixxxx")(ch 'I') 
test500 = TestCase  $ assertEqual "test500" (check parser7 "#\\Jxxxx")(ch 'J') 
test501 = TestCase  $ assertEqual "test501" (check parser7 "#\\Kxxxx")(ch 'K') 
test502 = TestCase  $ assertEqual "test502" (check parser7 "#\\Lxxxx")(ch 'L') 
test503 = TestCase  $ assertEqual "test503" (check parser7 "#\\Mxxxx")(ch 'M') 
test504 = TestCase  $ assertEqual "test504" (check parser7 "#\\Nxxxx")(ch 'N') 

test505 = TestCase  $ assertEqual "test505" (check parser7 "#\\Oxxxx")(ch 'O') 
test506 = TestCase  $ assertEqual "test506" (check parser7 "#\\Pxxxx")(ch 'P') 
test507 = TestCase  $ assertEqual "test507" (check parser7 "#\\Qxxxx")(ch 'Q') 
test508 = TestCase  $ assertEqual "test508" (check parser7 "#\\Rxxxx")(ch 'R') 
test509 = TestCase  $ assertEqual "test509" (check parser7 "#\\Sxxxx")(ch 'S') 
test510 = TestCase  $ assertEqual "test510" (check parser7 "#\\Txxxx")(ch 'T') 
test511 = TestCase  $ assertEqual "test511" (check parser7 "#\\Uxxxx")(ch 'U') 
test512 = TestCase  $ assertEqual "test512" (check parser7 "#\\Vxxxx")(ch 'V') 

test513 = TestCase  $ assertEqual "test513" (check parser7 "#\\Wxxxx")(ch 'W') 
test514 = TestCase  $ assertEqual "test514" (check parser7 "#\\Xxxxx")(ch 'X') 
test515 = TestCase  $ assertEqual "test515" (check parser7 "#\\Yxxxx")(ch 'Y') 
test516 = TestCase  $ assertEqual "test516" (check parser7 "#\\Zxxxx")(ch 'Z') 
test517 = TestCase  $ assertEqual "test517" (check parser7 "#\\0xxxx")(ch '0') 
test518 = TestCase  $ assertEqual "test518" (check parser7 "#\\1xxxx")(ch '1') 
test519 = TestCase  $ assertEqual "test519" (check parser7 "#\\2xxxx")(ch '2') 
test520 = TestCase  $ assertEqual "test520" (check parser7 "#\\3xxxx")(ch '3') 

test521 = TestCase  $ assertEqual "test521" (check parser7 "#\\4xxxx")(ch '4') 
test522 = TestCase  $ assertEqual "test522" (check parser7 "#\\5xxxx")(ch '5') 
test523 = TestCase  $ assertEqual "test523" (check parser7 "#\\6xxxx")(ch '6') 
test524 = TestCase  $ assertEqual "test524" (check parser7 "#\\7xxxx")(ch '7') 
test525 = TestCase  $ assertEqual "test525" (check parser7 "#\\8xxxx")(ch '8') 
test526 = TestCase  $ assertEqual "test526" (check parser7 "#\\9xxxx")(ch '9') 
test527 = TestCase  $ assertEqual "test527" (check parser7 "#\\!xxxx")(ch '!') 
test528 = TestCase  $ assertEqual "test528" (check parser7 "#\\$xxxx")(ch '$') 

test529 = TestCase  $ assertEqual "test529" (check parser7 "#\\%xxxx")(ch '%') 
test530 = TestCase  $ assertEqual "test530" (check parser7 "#\\&xxxx")(ch '&') 
test531 = TestCase  $ assertEqual "test531" (check parser7 "#\\|xxxx")(ch '|') 
test532 = TestCase  $ assertEqual "test532" (check parser7 "#\\*xxxx")(ch '*') 
test533 = TestCase  $ assertEqual "test533" (check parser7 "#\\+xxxx")(ch '+') 
test534 = TestCase  $ assertEqual "test534" (check parser7 "#\\-xxxx")(ch '-') 
test535 = TestCase  $ assertEqual "test535" (check parser7 "#\\/xxxx")(ch '/') 
test536 = TestCase  $ assertEqual "test536" (check parser7 "#\\:xxxx")(ch ':') 

test537 = TestCase  $ assertEqual "test537" (check parser7 "#\\<xxxx")(ch '<') 
test538 = TestCase  $ assertEqual "test538" (check parser7 "#\\=xxxx")(ch '=') 
test539 = TestCase  $ assertEqual "test539" (check parser7 "#\\?xxxx")(ch '?') 
test540 = TestCase  $ assertEqual "test540" (check parser7 "#\\>xxxx")(ch '>') 
test541 = TestCase  $ assertEqual "test541" (check parser7 "#\\@xxxx")(ch '@') 
test542 = TestCase  $ assertEqual "test542" (check parser7 "#\\^xxxx")(ch '^') 
test543 = TestCase  $ assertEqual "test543" (check parser7 "#\\_xxxx")(ch '_') 
test544 = TestCase  $ assertEqual "test544" (check parser7 "#\\~xxxx")(ch '~') 

test545 = TestCase  $ assertEqual "test545" (check parser7 "#\\`xxxx")(ch '`') 
test546 = TestCase  $ assertEqual "test546" (check parser7 "#\\'xxxx")(ch '\'') 
test547 = TestCase  $ assertEqual "test547" (check parser7 "#\\\"xxx")(ch '"') 
test548 = TestCase  $ assertEqual "test548" (check parser7 "#\\(xxxx")(ch '(') 
test549 = TestCase  $ assertEqual "test549" (check parser7 "#\\)xxxx")(ch ')') 
test550 = TestCase  $ assertEqual "test550" (check parser7 "#\\;xxxx")(ch ';') 
test551 = TestCase  $ assertEqual "test551" (check parser7 "#\\\\xxx")(ch '\\') 
test552 = TestCase  $ assertEqual "test552" (check parser7 "#\\,xxxx")(ch ',') 

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
  , test177,test178,test179,test180,test181,test182,test183,test184
  , test185,test186,test187,test188,test189,test190,test191,test192
  , test193,test194,test195,test196,test197,test198,test199,test200
  , test201,test202,test203,test204,test205,test206,test207,test208
  , test209,test210,test211,test212,test213,test214,test215,test216
  , test217,test218,test219,test220,test221,test222,test223,test224
  , test225,test226,test227,test228,test229,test230,test231,test232
  , test233,test234,test235,test236,test237,test238,test239,test240
  , test241,test242,test243,test244,test245,test246,test247,test248
  , test249,test250,test251,test252,test253,test254,test255,test256
  , test257,test258,test259,test260,test261,test262,test263,test264
  , test265,test266,test267,test268,test269,test270,test271,test272
  , test273,test274,test275,test276,test277,test278,test279,test280
  , test281,test282,test283,test284,test285,test286,test287,test288
  , test289,test290,test291,test292,test293,test294,test295,test296
  , test297,test298,test299,test300,test301,test302,test303,test304
  , test305,test306,test307,test308,test309,test310,test311,test312
  , test313,test314,test315,test316,test317,test318,test319,test320
  , test321,test322,test323,test324,test325,test326,test327,test328
  , test329,test330,test331,test332,test333,test334,test335,test336
  , test337,test338,test339,test340,test341,test342,test343,test344
  , test345,test346,test347,test348,test349,test350,test351,test352
  , test353,test354,test355,test356,test357,test358,test359,test360
  , test361,test362,test363,test364,test365,test366,test367,test368
  , test369,test370,test371,test372,test373,test374,test375,test376
  , test377,test378,test379,test380,test381,test382,test383,test384
  , test385,test386,test387,test388,test389,test390,test391,test392
  , test393,test394,test395,test396,test397,test398,test399,test400
  , test401,test402,test403,test404,test405,test406,test407,test408
  , test409,test410,test411,test412,test413,test414,test415,test416
  , test417,test418,test419,test420,test421,test422,test423,test424
  , test425,test426,test427,test428,test429,test430,test431,test432
  , test433,test434,test435,test436,test437,test438,test439,test440
  , test441,test442,test443,test444,test445,test446,test447,test448
  , test449,test450,test451,test452,test453,test454,test455,test456
  , test457,test458,test459,test460,test461,test462,test463,test464
  , test465,test466,test467,test468,test469,test470,test471,test472
  , test473,test474,test475,test476,test477,test478,test479,test480
  , test481,test482,test483,test484,test485,test486,test487,test488
  , test489,test490,test491,test492,test493,test494,test495,test496
  , test497,test498,test499,test500,test501,test502,test503,test504
  , test505,test506,test507,test508,test509,test510,test511,test512
  , test513,test514,test515,test516,test517,test518,test519,test520
  , test521,test522,test523,test524,test525,test256,test527,test528
  , test529,test530,test531,test532,test533,test534,test535,test536
  , test537,test538,test539,test540,test541,test542,test543,test544
  , test545,test546,test547,test548,test549,test550,test551,test552
  ]

