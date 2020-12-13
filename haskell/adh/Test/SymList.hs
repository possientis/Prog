module  Test.SymList
    (   specSymList
    )   where

import Test.Hspec
import Test.QuickCheck

import SymList

specSymList :: Spec
specSymList = do
    specToFrom
    specFromTo
    specNil
    specCons
    specSnoc

specToFrom :: Spec
specToFrom = it "Checked toSL (fromSL sl) == sl" $ property propToFrom

specFromTo :: Spec
specFromTo = it "Checked fromSL (toSL xs) == xs" $ property propFromTo

specNil :: Spec
specNil = it "Checked nilSL is []" $ do
    fromSL (nilSL) `shouldBe` ([] :: [Int])

specCons :: Spec
specCons = it "Checked cons x . fromSL = fromSL . consSL x" $
    property propCons

specSnoc :: Spec
specSnoc = it "Checked snoc x . fromSL = fromSL . snoc x" $
    property propSnoc

propToFrom :: SymList Int -> Bool
propToFrom xs = toSL (fromSL xs) == xs

propFromTo :: [Int] -> Bool
propFromTo xs = fromSL (toSL xs) == xs

propCons :: Int -> SymList Int -> Bool
propCons x xs = x : fromSL xs == fromSL (consSL x xs)

propSnoc :: Int -> SymList Int -> Bool
propSnoc x xs = fromSL xs ++ [x] == fromSL (snocSL x xs)

