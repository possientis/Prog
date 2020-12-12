module  SymList
    (   SymList (..) 
    ,   fromSL
    ,   toSL
    ,   consSL
    ,   snocSL
    ,   headSL
    ,   lastSL
    ,   tailSL
    ,   initSL
    ,   nilSL
    ,   main
    )   where

import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec specTest

data SymList a = SymList
    { start :: [a]
    , end   :: [a]
    } deriving (Show)

instance Eq a => Eq (SymList a) where
    (==) (SymList xs ys) (SymList xs' ys') 
        = xs ++ reverse ys == xs' ++ reverse ys'

single :: [a] -> Bool
single [_] = True
single _   = False

nilSL :: SymList a
nilSL = SymList [] []

fromSL :: SymList a -> [a]
fromSL (SymList xs ys) = xs ++ reverse ys

toSL :: [a] -> SymList a
toSL xs = SymList us (reverse vs)
    where (us,vs) = splitAt (length xs `div` 2) xs

consSL :: a -> SymList a -> SymList a
consSL x (SymList xs ys) = if null ys
    then (SymList [x] xs)
    else (SymList (x:xs) ys)

snocSL :: a -> SymList a -> SymList a
snocSL x (SymList xs ys) = if null xs 
    then (SymList ys [x])
    else (SymList xs (x:ys))

headSL :: SymList a -> a
headSL (SymList xs ys) = if null xs
    then head ys
    else head xs

lastSL :: SymList a -> a
lastSL (SymList xs ys) = if null ys 
    then head xs 
    else head ys

tailSL :: SymList a -> SymList a
tailSL (SymList xs ys)
    | null xs   =  if null ys then error "tailSL: empty list" else nilSL
    | single xs = SymList (reverse vs) us
    | otherwise = SymList (tail xs) ys
    where (us,vs) = splitAt (length ys `div` 2) ys
    

initSL :: SymList a -> SymList a
initSL = undefined

specTest :: Spec
specTest = do
    specToFrom

specToFrom :: Spec
specToFrom = it "Check toSL (fromSL sl) == sl" $ property propToFrom

propToFrom :: [Int] -> [Int] -> Bool
propToFrom xs ys = toSL (fromSL (SymList xs ys)) == SymList xs ys


