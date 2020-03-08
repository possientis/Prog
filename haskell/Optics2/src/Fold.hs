{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}

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
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7
    )   where

import Control.Lens
import Data.Set as S
import Data.Map as M

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
crewRole :: Fold CrewMember Role
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

