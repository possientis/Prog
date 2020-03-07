{-# LANGUAGE TemplateHaskell    #-}

module  Fold
    (   Role        (..)
    ,   CrewMember  (..)
    ,   name
    ,   role
    ,   talents
    ,   roster
    ,   myFold
    )   where

import Control.Lens
import Data.Set as S

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
 
