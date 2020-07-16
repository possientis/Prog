{-# LANGUAGE LambdaCase             #-}

module  Poly
    (   Poly    (..)
    ,   main
    )   where

import Test.Hspec
import Test.QuickCheck
import Data.Bifunctor
import Data.Functor.Foldable

newtype Poly a = Poly { unPoly :: [a] } 

main :: IO ()
main = hspec $ describe "Testing equivalence of implementations" $ do
    spec01

spec01 :: Spec
spec01 = it "Checked eval0 ~ eval1" $ do
    property prop01

prop01 :: [Integer] -> Integer -> Bool
prop01 xs x = eval0 (Poly xs) x == eval1 (Poly xs) x 

pow :: (Num a) => a -> Integer -> a
pow x n
    | n < 0     = error "pow: negative argument"
    | n == 0    = 1
    | otherwise = x * pow x (n - 1)

-- initial type of bifunctor ListF
mu :: ListF a [a] -> [a]
mu = \case
    Nil         -> []
    Cons x xs   -> x : xs

triangle_ :: (a -> a) -> ListF a [a] -> [a]
triangle_ f = mu . bimap id (map f) 

triangle :: (a -> a) -> [a] -> [a]
triangle = cata . triangle_

eval0 :: (Num a) => Poly a -> a -> a
eval0 p x = sum $ map (\(a,n) -> a * pow x n) $ zip (unPoly p) [0..]

eval1 :: (Num a) => Poly a -> a -> a
eval1 p x = sum $ triangle (*x) $ unPoly p 

