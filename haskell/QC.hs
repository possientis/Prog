import Test.QuickCheck
import Control.Monad (liftM, liftM2)
import Prettify

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


main = do
  check_empty_id
  check_char








