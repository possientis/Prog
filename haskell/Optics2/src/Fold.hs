{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE OverloadedStrings  #-}

module  Fold
    (   Role        (..)
    ,   CrewMember  (..)
    ,   name
    ,   role
    ,   talents
    ,   roster
    ,   myFold
    ,   crewMembers
    ,   crewRole
    ,   toListSomehow
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11, ex12, ex13, ex14, ex15
    )   where

import Data.Set         as S
import Data.Map         as M
import Data.Text
import Data.Word
import Control.Lens
import Data.ByteString

data Role
    = Gunner
    | PowderMonkey
    | Navigator
    | Captain
    | FirstMate
    deriving (Show, Eq, Ord)

data CrewMember = CrewMember
    { _name     :: String
    , _role     :: Role
    , _talents  :: [String]
    } deriving (Show, Eq, Ord)

makeLenses ''CrewMember

roster :: Set CrewMember
roster = S.fromList
    --
    [ CrewMember "Grumpy Roger"     Gunner          ["Juggling", "Arbitrage"]
    , CrewMember "Long-John Bronze" PowderMonkey    ["Origami"]
    , CrewMember "Salty Steve"      PowderMonkey    ["Charcuterie"]
    , CrewMember "One-eyed Jack"    Navigator       []
    ]

myFold :: Fold s a
myFold = undefined
 
-- folded :: Foldable f => Fold (f a) a
-- toListOf :: Fold s a -> s -> [a]
-- (^..) :: s -> Fold s a -> [a]
-- (^..) = flip toListOf

crewMembers :: Fold (Set CrewMember) CrewMember
crewMembers = folded

-- lenses can be used as Folds
--crewRole :: Fold CrewMember Role
crewRole :: Lens' CrewMember Role -- avoiding compiler warning
crewRole = role

toListSomehow :: Fold (Set CrewMember) Role -> Set CrewMember -> [Role]
toListSomehow = toListOf

ex1 :: [CrewMember]
ex1 = toListOf folded roster

ex2 :: [CrewMember]
ex2 = roster ^.. folded

-- Maybe is foldable
ex3 :: [String]
ex3 = Just "Buried Treasure" ^.. folded     -- ["Buried Treasure"]

ex4 :: [String]
ex4 = Nothing ^.. folded                    -- []

ex5 :: [String]
ex5 = Identity "Cutglass" ^.. folded        -- ["Cutglass"]

-- Foldable instance of tuple only focusses the right-hand value
ex6 :: [String]
ex6 = ("Rubies", "Gold") ^.. folded         -- ["Gold"]

-- Folding a map focusses only the values, not the keys
ex7 :: [String]
ex7 = M.fromList [("Jack", "Captain"),("Will", "First Mate")] ^.. folded

-- both :: Bitraversable r => Traversal (r a a) (r b b) a b
-- in spirit:
-- both :: Bitraversable r => Fold (r a a) a

ex8 :: [String] 
ex8 = ("Gemini", "Leo") ^.. both


ex9 :: [String]
ex9 = Left "Albuquerque" ^.. both

ex10 :: [String]
ex10 =  Right "Yosemite" ^.. both

ex11 :: [String]
ex11 = ("Gemini", "Leo", "Libra") ^.. both

-- each :: Each s t a b => Traversal s t a b
-- Simplified
-- each :: Each s s a a => Fold s a

ex12 :: [Int]
ex12 = (1,2,3,4,5) ^.. each

ex13 :: [Int]
ex13 = [1,2,3,4,5] ^.. each


ex14 :: String
ex14 = ("Made him an offer he couldn't refuse" :: Text) ^.. each


ex15 :: [Word8]
ex15 = ("Do or do not" :: ByteString) ^.. each

beastSizes :: [(Int,String)]
beastSizes = [(3,"Sirens"), (882,"Kraken"), (92,"Ogopogo")]

ex16 = beastSizes ^.. folded 

ex17 = beastSizes ^.. folded . folded

ex18 = beastSizes ^.. folded . folded . folded

ex19 = beastSizes ^.. folded . _2

ex20 = toListOf (folded . folded) [[1,2,3],[4,5,6]]


ex21 = toListOf
    (folded . folded)
    (M.fromList [("Jack","Captain"), ("Will", "First Mate")] :: Map String String)

ex22 = ("Hello", "It's me" :: String) ^.. both . folded


