module Steep
    (   main
    ,   steep1
    )   where

import Test.Hspec
import Test.QuickCheck
--import Data.Functor.Foldable

main :: IO ()
main = hspec $ describe "Testing equivalence of implementations" $ do
    spec1

spec1 :: Spec
spec1 = it "Checked steep1 ~ steep1" $ do
    property prop1 

prop1 :: [Int] -> Bool
prop1 xs = steep1 xs == steep1 xs

-- Quadratic complexity. Need to find implementation with linear complexity.
steep1 :: (Num a, Ord a) => [a] -> Bool
steep1 [] = True
steep1 (x : xs) = x > sum xs && steep1 xs


