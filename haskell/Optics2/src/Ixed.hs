{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE OverloadedStrings  #-}

module  Ixed
    (   Ixed    (..)
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8
    )   where

import Data.Map
import Data.Word
import Data.Text
import Control.Lens      as L hiding (Index, IxValue, Ixed)
import Data.ByteString

class Ixed m where
    ix :: Index m -> Traversal' m (IxValue m)

type family Index m
type family IxValue m

type instance Index [a] = Int
type instance IxValue [a] = a

type instance Index (Map k a) = k
type instance IxValue (Map k a) = a

type instance Index ByteString = Int
type instance IxValue ByteString = Word8

type instance Index Text = Int
type instance IxValue Text = Char


humanoids :: [String]
humanoids = ["Borg","Cardassian","Talaxian"]

ex1 :: Maybe String
ex1 = humanoids ^? L.ix 1

ex2 :: Maybe String
ex2 = humanoids ^? L.ix 5

ex3 :: [String]
ex3 = humanoids & L.ix 1 .~ "Vulcan"

ex4 :: [String]
ex4 = humanoids & L.ix 10 .~ "Vulcan"

benders :: Map String String
benders = fromList [("Katara","Water"), ("Toph","Earth"), ("Zuko","Fire")]

ex5 :: Maybe String
ex5 = benders ^? L.ix "Zuko"

ex6 :: Maybe String
ex6 = benders ^? L.ix "Missing"

ex7 :: Map String String
ex7 = benders & L.ix "Toph" .~ "Metal"

ex8 :: Map String String
ex8 = benders & L.ix "Missing" .~ "WontHappen"

ex9 :: Maybe Char
ex9 = ("hello" :: Text) ^? L.ix 0

ex10 :: Maybe Char
ex10 = ("hello" :: Text) ^? L.ix 10

ex11 :: Text
ex11 = ("hello" :: Text) & L.ix 0 .~ 'j'

ex12 :: Maybe Word8
ex12 = ("hello" :: ByteString) ^? L.ix 0

ex13 :: Maybe Word8
ex13 = ("hello" :: ByteString) ^? L.ix 10

ex14 :: ByteString
ex14 = ("hello" :: ByteString) & L.ix 0 +~ 2

ex15 :: [Text]
ex15 = ("hello" :: Text) & L.ix 1 %%~ \_ -> ("aeiou" :: [Char])








