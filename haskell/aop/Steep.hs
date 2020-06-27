{-# LANGUAGE LambdaCase             #-}

module Steep
    (   main
    ,   steep1
    )   where

import Test.Hspec
import Test.QuickCheck
import Data.Functor.Foldable

main :: IO ()
main = hspec $ describe "Testing equivalence of implementations" $ do
    spec1
    spec2
    spec3

spec1 :: Spec
spec1 = it "Checked steep1 ~ steep2" $ do
    property prop1 

spec2 :: Spec
spec2 = it "Checked fst . steep2_ == sum" $ do
    property prop2 

spec3 :: Spec
spec3 = it "Checked steep2 (x : xs) == x > sum xs && steep2 xs" $ do
    property prop3 

prop1 :: [Int] -> Bool
prop1 xs = steep1 xs == steep2 xs

prop2 :: [Int] -> Bool
prop2 xs = (fst . steep2_) xs == sum xs

prop3 :: Int -> [Int] -> Bool
prop3 x xs = steep2 (x : xs) == (x > sum xs && steep2 xs)

-- Quadratic complexity. Need to find implementation with linear complexity.
steep1 :: (Num a, Ord a) => [a] -> Bool
steep1 [] = True
steep1 (x : xs) = x > sum xs && steep1 xs

steep2_ :: (Num a, Ord a) => [a] -> (a,Bool)
steep2_ = cata $ \case
    Nil             -> (0,True)
    Cons x (s,b)    -> (s + x, x > s && b)

steep2 :: (Num a, Ord a) => [a] -> Bool
steep2 = snd . steep2_

