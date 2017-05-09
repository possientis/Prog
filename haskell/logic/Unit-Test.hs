import FirstOrder
import V
import Formula
import GFormula

import Test.HUnit

type TFormula = Formula    -- choose implementation

p1 = belong x y :: TFormula V
p2 = bot        :: TFormula V
p3 = imply p1 p2
p4 = forall x p1

f :: V -> Int
f v | v == x    = 0
    | v == y    = 1
    | v == z    = 2
    | otherwise = 3

test1   = TestCase $ assertEqual  "Eq.1"    p1 p1
test2   = TestCase $ assertEqual  "Eq.2"    p2 p2
test3   = TestCase $ assertEqual  "Eq.3"    p3 p3
test4   = TestCase $ assertEqual  "Eq.4"    p4 p4
test5   = TestCase $ assertBool   "Eq.5"    (p1 /= p2)
test6   = TestCase $ assertBool   "Eq.6"    (p2 /= p1)
test7   = TestCase $ assertBool   "Eq.7"    (p1 /= p3)
test8   = TestCase $ assertBool   "Eq.8"    (p3 /= p1)
test9   = TestCase $ assertBool   "Eq.9"    (p1 /= p4)
test10  = TestCase $ assertBool   "Eq.10"   (p4 /= p1)
test11  = TestCase $ assertBool   "Eq.11"   (p2 /= p3)
test12  = TestCase $ assertBool   "Eq.12"   (p3 /= p2)

test13  = TestCase $ assertEqual  "Show.1"  (show p1) "x:y"
test14  = TestCase $ assertEqual  "Show.2"  (show p2) "!"
test15  = TestCase $ assertEqual  "Show.3"  (show p3) "(x:y -> !)"
test16  = TestCase $ assertEqual  "Show.4"  (show p4) "Ax.x:y"

test17  = TestCase $ assertEqual  "fmap.1"  (f <$> p1) (belong 0 1) 
test18  = TestCase $ assertEqual  "fmap.2"  (f <$> p2) (bot)
test19  = TestCase $ assertEqual  "fmap.3"  (f <$> p3) $ imply (belong 0 1) bot
test20  = TestCase $ assertEqual  "fmap.4"  (f <$> p4) $ forall 0 (belong 0 1)
test21  = TestCase $ assertEqual  "fmap.5"  (id <$> p1) p1
test22  = TestCase $ assertEqual  "fmap.6"  (id <$> p2) p2
test23  = TestCase $ assertEqual  "fmap.7"  (id <$> p3) p3
test24  = TestCase $ assertEqual  "fmap.8"  (id <$> p4) p4



test_Eq = TestLabel "test_Eq" $ TestList
  [ test1,    test2,    test3,    test4,    test5
  , test6,    test7,    test8,    test9,    test10
  , test11,   test12,   test13,   test14,   test15
  , test16,   test17,   test18,   test19,   test20
  , test21,   test22,   test23,   test24
  ]

tests = TestList [ test_Eq ]

main = do
  runTestTT tests




