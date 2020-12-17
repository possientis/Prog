module  Test.SymList
    (   specSymList
    )   where

import RIO.List

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
    specReverse
    specHead
    specLast
    specTail
    specInit
    specNull
    specSingle
    specLength

specToFrom :: Spec
specToFrom = it "Checked toSL (fromSL xs) == xs" $ property propToFrom

specFromTo :: Spec
specFromTo = it "Checked fromSL (toSL xs) == xs" $ property propFromTo

specNil :: Spec
specNil = it "Checked nilSL is []" $ do
    fromSL (nilSL) `shouldBe` ([] :: [Int])

specCons :: Spec
specCons = it "Checked cons x . fromSL == fromSL . consSL x" $
    property propCons

specSnoc :: Spec
specSnoc = it "Checked snoc x . fromSL == fromSL . snoc x" $
    property propSnoc

specReverse :: Spec
specReverse = it "Checked reverse (from SL xs) == fromSL (reverseSL xs)" $ 
    property propReverse

specHead :: Spec
specHead = it "Checked headMaybe (fromSL xs) == headSL xs" $
    property propHead

specLast :: Spec
specLast = it "Checked lastMaybe (fromSL xs) == lastSL xs" $
    property propLast

specTail :: Spec
specTail = it "Checked tailMaybe (fromSL xs) == (fromSL <$> tailSL xs)" $
    property propTail

specInit :: Spec
specInit = it "Checked initMaybe (fromSL xs) == (fromSL <$> initSL xs)" $
    property propInit

specNull :: Spec
specNull = it "Checked null (fromSL xs) == nullSL xs" $
    property propNull

specSingle :: Spec
specSingle = it "Checked single (fromSL xs) == singleSL xs" $
    property propSingle

specLength :: Spec
specLength = it "Checked length (fromSL xs) == lengthSL xs" $
    property propLength

propToFrom :: SymList Int -> Bool
propToFrom xs = toSL (fromSL xs) == xs

propFromTo :: [Int] -> Bool
propFromTo xs = fromSL (toSL xs) == xs

propCons :: Int -> SymList Int -> Bool
propCons x xs = x : fromSL xs == fromSL (consSL x xs)

propSnoc :: Int -> SymList Int -> Bool
propSnoc x xs = fromSL xs ++ [x] == fromSL (snocSL x xs)

propReverse :: SymList Int -> Bool
propReverse xs = reverse (fromSL xs) == fromSL (reverseSL xs)

propHead :: SymList Int -> Bool
propHead xs = headMaybe (fromSL xs) == headSL xs

propLast :: SymList Int -> Bool
propLast xs = lastMaybe (fromSL xs) == lastSL xs

propTail :: SymList Int -> Bool
propTail xs = tailMaybe (fromSL xs) == (fromSL <$> tailSL xs)

propInit :: SymList Int -> Bool
propInit xs = initMaybe (fromSL xs) == (fromSL <$> initSL xs)

propNull :: SymList Int -> Bool
propNull xs = null (fromSL xs) == nullSL xs

propSingle :: SymList Int -> Bool
propSingle xs = single (fromSL xs) == singleSL xs

propLength :: SymList Int -> Bool
propLength xs = length (fromSL xs) == lengthSL xs
