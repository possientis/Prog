import Test.QuickCheck
import Control.Monad (liftM, liftM2)
import Prettify
import Data.List (intersperse)


{-
data Doc  = Empty
          | Char Char
          | Text String
          | Line 
          | Concat Doc Doc
          | Union Doc Doc
            deriving (Show, Eq)
-}

{- 
-- This is a verbose way of generating random Doc
instance Arbitrary Doc where
  arbitrary = do 
    n <- choose (1,6) :: Gen Int
    case n of 
      1 -> return Empty
      2 -> do
        x <- arbitrary  -- type inference will work it out
        return (Char x) -- there! Compiler now knows x :: Char
      3 -> do
        x <- arbitrary 
        return (Text x)
      4 -> return Line
      5 -> do
        x <- arbitrary
        y <- arbitrary
        return (Concat x y)
      6 -> do
        x <- arbitrary
        y <- arbitrary
        return (Union x y)
-}          

instance Arbitrary Doc where
  arbitrary = 
    oneof   [ return Empty
            , liftM Char arbitrary
            , liftM Text arbitrary
            , return Line
            , liftM2 Concat arbitrary arbitrary
            , liftM2 Union arbitrary arbitrary ]

test1 = arbitrary :: Gen Doc  -- Gen Doc
test2 = generate test1        -- IO Doc


prop_empty_id :: Doc -> Bool
prop_empty_id x = empty <> x == x && x <> empty == x
check_empty_id = quickCheck prop_empty_id

test4 = verboseCheck prop_empty_id


prop_char :: Char -> Bool
prop_char c = char c == Char c
check_char  = quickCheck prop_char


prop_text :: String -> Bool
prop_text s = text s == if null s then Empty else Text s
check_text = quickCheck prop_text

prop_line :: Bool
prop_line = line == Line
check_line = quickCheck prop_line

prop_double :: Double -> Bool
prop_double d = double d == Text (show d)
check_double = quickCheck prop_double

prop_hcat :: [Doc] -> Bool
prop_hcat xs = hcat xs == glue xs 
  where
    glue [] = empty
    glue (d:ds) = d <> glue ds
check_hcat = quickCheck prop_hcat
test5 = verboseCheck prop_hcat

prop_punctuate :: Doc -> [Doc] -> Bool
prop_punctuate s xs = punctuate s xs == combine (intersperse s xs)
  where
    combine []  = []
    combine [x] = [x]
    combine (x:Empty:ys) = x:combine ys
    combine (Empty:y:ys) = y:combine ys
    combine (x:y:ys)     = x `Concat` y : combine ys

check_punctuate = quickCheck prop_punctuate

{-
-- can't find this defined anywhere
options = TestOptions { no_of_tests     = 200
                      , length_of_tests = 1
                      , debug_tests     = False }
-}


main = do
  check_empty_id
  check_char
  check_text
  check_line
  check_double
  check_hcat
  check_punctuate








