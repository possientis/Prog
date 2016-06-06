import Data.Array (Array(..), (!), bounds, elems, indices, ixmap, listArray)
import Control.Applicative ((<$>))
import Control.Monad (forM)
import Data.Char (digitToInt)
import Data.Ix (Ix(..))
import Data.List (foldl', group, sort, sortBy, tails)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Ratio (Ratio)
import Data.Word (Word8)
import System.Environment (getArgs)
import qualified Data.ByteString.Lazy.Char8 as L
import qualified Data.Map as M
import Parse

mapEveryOther :: (a -> a) -> [a] -> [a]
mapEveryOther f = zipWith ($) (cycle [f,id])

test0 = mapEveryOther (\x -> x * x) [2,3,4,5,6,7,8,9,10]  -- [4,3,16,5,36,7,64,9,100]

checkDigit :: (Integral a) => [a] -> a
checkDigit ds = 10 - (sum products `mod` 10)
  where products = mapEveryOther (*3) (reverse ds)

leftOddList =  ["0001101", "0011001", "0010011", "0111101", "0100011",
                "0110001", "0101111", "0111011", "0110111", "0001011"]

-- leftOddList :: [[Char]]
-- complement :: Char -> Char
-- map :: (a -> b) -> [a] -> [b]
-- =================================
-- map complement :: [Char] -> [Char]
-- =================================
-- (map complement <$>) :: [[Char]] -> [[Char]]
--
-- recall that (<$>) is just an infix alias of fmap, which in this case
-- is applied to the list Functor [..], hence fmap is map. Hence the code
-- below is equivalent to: map (map complement) leftOddList

{-
               ["1110010","1100110","1101100","1000010","1011100","1001110",
                "1010000","1000100","1001000","1110100"]
-}
rightList = map complement <$> leftOddList -- aka map (map complement) leftOddList
  where complement '0' = '1'
        complement '1' = '0'

{-
               ["0100111","0110011","0011011","0100001","0011101","0111001",
                "0000101","0010001","0001001","0010111"]
-}
leftEvenList = map reverse rightList

parityList = ["111111", "110100", "110010", "110001", "101100",
              "100110", "100011", "101010", "101001", "100101"]

listToArray :: [a] -> Array Int a
listToArray xs = listArray (0,l-1) xs
  where l = length xs

leftOddCodes, leftEvenCodes, rightCodes, parityCodes :: Array Int String
leftOddCodes = listToArray leftOddList
leftEvenCodes = listToArray leftEvenList
rightCodes = listToArray rightList
parityCodes = listToArray parityList

test1 = listArray (0,2) "foo"   -- array (0,2) [(0,'f'),(1,'o'),(2,'o')]
test2 = test1 ! 0
-- array ('a','h') 
-- [('a',97),('b',98),('c',99),('d',100),('e',101),('f',102),('g',103),('h',104)]
test3 = listArray ('a','h')[97..]
test4 = test3 ! 'e'       -- 101
test5 = listArray ((0,0,0),(9,9,9)) [0..]
test6 = test5 ! (4,3,7)   -- 437

-- indices :: Ix i => Array i e -> [i]
indices1 = indices test3  -- "abcdefgh"
indices2 = indices test5  -- [(0,0,0),(0,0,1),(0,0,2), ......., (9,9,9)]


test7 = listArray (0,5) "bar"
test8 = test7 !2  -- 'r' , no error yet...lazy
test9 = test7 ! 3 -- still no error, until attempting to compute test9 
-- it is possible to use 'strict' arrays too (as opposed to 'lazy' arrays here)

-- Strict left fold, similar to foldl' on lists.
foldA :: Ix k => (a -> b -> a) -> a -> Array k b -> a
foldA f s a = go s (indices a)
  where go s (j:js) = let s' = f s (a ! j)
                      in s' `seq` go s' js  -- seq forces evaluation of s'
        go s _      = s                     -- hence avoids space blow up
                                            -- note that 'go' is tail recursive
-- Strict left fold using the first element of the array as its starting value
foldA1 :: Ix k => (a -> a -> a) -> Array k a -> a
foldA1 f a = foldA f (a ! fst (bounds a)) a







