{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE RankNTypes         #-}

module  Ixed
    (   Ixed    (..)
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


