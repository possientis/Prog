module  SymList
    (   SymList (..) 
    ,   fromSL
    ,   toSL
    ,   reverseSL
    ,   nilSL
    ,   consSL
    ,   snocSL
    ,   headSL
    ,   lastSL
    ,   tailSL
    ,   initSL
    ,   nullSL
    ,   single
    ,   singleSL
    ,   lengthSL
    )   where

import Test.QuickCheck

-- Data structure invariant:
-- null start -> null end   \/ single end
-- null end   -> null start \/ single start
-- i.e. Never allow one part to [] if the other part has more than 1 element.
-- API implementation should ensure this invariant is never broken.
data SymList a = SymList
    { start :: [a]
    , end   :: [a]
    } deriving (Show)

instance Eq a => Eq (SymList a) where
    (==) (SymList xs ys) (SymList xs' ys') 
        = xs ++ reverse ys == xs' ++ reverse ys'

instance (Arbitrary a) => Arbitrary (SymList a) where
    arbitrary = toSL <$> arbitrary

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

reverseSL :: SymList a -> SymList a
reverseSL (SymList xs ys) = SymList ys xs

consSL :: a -> SymList a -> SymList a
consSL x (SymList xs ys) = if null ys
    then (SymList [x] xs)
    else (SymList (x:xs) ys)

snocSL :: a -> SymList a -> SymList a
snocSL x (SymList xs ys) = if null xs 
    then (SymList ys [x])
    else (SymList xs (x:ys))

headSL :: SymList a -> Maybe a
headSL (SymList xs ys) = if null xs
    then if null ys then Nothing else Just (head ys)
    else Just (head xs)

lastSL :: SymList a -> Maybe a
lastSL (SymList xs ys) = if null ys 
    then if null xs then Nothing else Just (head xs)
    else Just (head ys)

tailSL :: SymList a -> Maybe (SymList a)
tailSL (SymList xs ys)
    | null xs   =  if null ys then Nothing else Just nilSL
    | single xs = Just $ reverseSL (toSL ys)
    | otherwise = Just $ SymList (tail xs) ys
    
initSL :: SymList a -> Maybe (SymList a)
initSL (SymList xs ys)
    | null ys   = if null xs then Nothing else Just nilSL
    | single ys = Just $ toSL xs
    | otherwise = Just $ SymList xs (tail ys)

nullSL :: SymList a -> Bool
nullSL (SymList xs ys) = null xs && null ys

singleSL :: SymList a -> Bool
singleSL (SymList xs ys) = (single xs && null ys) || (null xs && single ys)

lengthSL :: SymList a -> Int
lengthSL (SymList xs ys) = length xs + length ys
