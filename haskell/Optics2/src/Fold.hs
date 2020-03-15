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
    ,   setCrewMembers
    ,   crewRole
    ,   toListSomehow
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11, ex12, ex13, ex14, ex15
    ,   shipName
    ,   captain
    ,   firstMate
    ,   conscripts
    )   where

import Prelude          as P
import Data.Set         as S
import Data.Map         as M
import Data.Text        hiding (toUpper)
import Data.Char        
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

setCrewMembers :: Fold (Set CrewMember) CrewMember
setCrewMembers = folded

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


newtype Name = Name
    { getName :: String
    } deriving Show

data ShipCrew = ShipCrew
    { _shipName   :: Name
    , _captain    :: Name
    , _firstMate  :: Name
    , _conscripts :: [Name]
    } deriving (Show)

makeLenses ''ShipCrew

collectCrewMembers :: ShipCrew -> [Name]
collectCrewMembers crew = [crew ^. captain, crew ^. firstMate] ++ crew ^. conscripts

-- folding :: Foldable f => (s -> f a) -> Fold s a
crewMembers :: Fold ShipCrew Name
crewMembers = folding collectCrewMembers


myCrew :: ShipCrew
myCrew = ShipCrew
    { _shipName   = Name "Purple Pearl"
    , _captain    = Name "Grumpy Roger"
    , _firstMate  = Name " Long-John Bronze"
    , _conscripts = [Name "One-eyed Jack", Name "Filthy Frank"]
    }


ex23 = myCrew ^.. crewMembers

-- to :: (s -> a) -> Fold s a

ex24 = Name "Two-faced Tony" ^. to getName

ex25 = Name "Two-faced Tony" ^. to getName . to (fmap toUpper)

ex26 = Name "Two-faced Tony" ^. to (fmap toUpper . getName)

ex27 = myCrew ^.. crewMembers . to getName

ex28 = P.map getName $ myCrew ^.. crewMembers

crewNames :: Fold ShipCrew Name
crewNames = folding $ \s 
    -> s ^.. captain
    <> s ^.. firstMate
    <> s ^.. conscripts . folded

crewNames2 :: Fold ShipCrew Name
crewNames2 = folding $ \s -> [s ^. captain, s ^. firstMate] ++ s ^. conscripts

-- elemOf :: Eq a => Fold s a -> a -> s -> Bool
ex29 = elemOf folded 3 [1,2,3,4]

ex30 = elemOf folded 99 [1,2,3,4]

-- anyOf :: Fold s a => (a -> Bool) -> s -> Bool (not quite the expected sig)
ex31 = anyOf folded even [1,2,3,4]

ex32 = anyOf folded (>10) [1,2,3,4]


-- allOf :: Fold s a -> (a -> Bool) -> s -> Bool
ex33 = allOf folded even [1,2,3,4]

ex34 = allOf folded (<10) [1,2,3,4]


-- findOf :: Fold s a -> (a -> Bool) -> s -> Maybe a
ex35 = findOf folded even [1,2,3,4]

ex36 = findOf folded (>10) [1,2,3,4]

-- has :: Fold s a -> s -> Bool
-- hasn't :: Fold s a -> s -> Bool

ex37 = has folded []

ex38 = has folded [1,2]

ex39 = hasn't folded []

ex40 = hasn't folded [1,2]

-- lengthOf :: Fold s a -> s -> Int
ex41 = lengthOf folded [1,2,3,4]

-- sumOf :: Num a => Fold s a -> s -> a
-- productOf :: Num a => Fold s a -> s -> a

ex42 = sumOf folded [1,2,3,4]
ex43 = productOf folded [1,2,3,4]

-- same thing for Fold
-- firstOf :: Fold s a -> s -> Maybe a
-- preview :: Fold s a -> s -> Maybe a
-- (^?)    :: s -> Fold s a -> Maybe a
ex44 = firstOf folded []
ex45 = firstOf folded [1,2,3,4]
ex46 = preview folded [1,2,3,4]
ex47 = [1,2,3,4] ^? folded

-- lastOf :: Fold s a -> s -> Maybe a
ex48 = lastOf folded [1,2,3,4]

-- minimOf :: Ord a => Fold s a -> s -> Maybe a
-- maximumOf :: Ord a => Fold s a -> s -> Maybe a

ex49 = minimumOf folded [2,1,4,3] :: Maybe Int
ex50 = maximumOf folded [2,1,4,3] :: Maybe Integer
ex51 = minimumOf folded []        :: Maybe Integer
ex52 = maximumOf folded []        :: Maybe Int

