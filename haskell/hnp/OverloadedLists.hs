{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}

import GHC.Exts

import qualified Data.Map       as M
import qualified Data.Set       as S
import qualified Data.Vector    as V
import qualified Data.Text      as T

dict :: M.Map String Int
dict = [("foo", 1), ("bar",2)] 

set :: S.Set Char
set = ['0' .. '9']


vect :: V.Vector Int
vect = [1..10]

text :: T.Text
text = ['a' .. 'z']

{-
instance IsList [a] where
    type Item [a] = a
    fromList = id
    toList   = id
-}

data List a = Nil | Cons a (List a)

instance IsList (List a) where
    type Item (List a) = a

    fromList []         = Nil
    fromList (x:xs)     = Cons x (fromList xs)

    toList Nil          = []
    toList (Cons x xs)  = x:toList xs 

data NatList = Nul | Con Int NatList

instance IsList NatList where
    type Item NatList = Int 

    fromList []         = Nul
    fromList (n:ns)     = Con n (fromList ns)

    toList Nul          = []
    toList (Con n ns)   = n:toList ns

{-
instance (Ord a) => IsList (S.Set a) where
    type Item (S.Set a) = a
    fromList = S.fromList
    toList   = S.toList
-}

main :: IO ()
main = do
    print $ M.lookup "foo" dict -- Just 1

