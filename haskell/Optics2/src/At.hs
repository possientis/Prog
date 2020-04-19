{-# LANGUAGE RankNTypes         #-}

module  At
    (   ex1, ex2, ex3, ex4, ex5
    ,   At  (..)
    )   where

import Data.Map
import Control.Lens as L hiding (sans, At (..))
import qualified Control.Lens as L (sans, At (..))

turtles :: Map String String
turtles = fromList [("Leo","Katanas"),("Raph","Sai")]

ex1 :: Map String String
ex1 = insert "Mikey" "Nunchaku" turtles

ex2 :: Map String String
ex2 = delete "Leo" turtles


class At m where 
    at :: Index m -> Lens' m (Maybe (IxValue m))


benders :: Map String String
benders = fromList [("Katara","Water"), ("Toph","Earth"), ("Zuko","Fire")]

-- 'at' creates a lens, we can use `^.` instead of `^?`
ex3 :: Maybe String
ex3 = benders ^. L.at "Zuko"

-- delete from Map-like structure
ex4 :: Map String String
ex4 = benders & L.at "Zuko" .~ Nothing

-- add entry to Map-like structure
ex5 :: Map String String
ex5 = benders & L.at "Missing" .~ Just "New Entry"

-- (?~) :: Traversal s t a (Maybe b) -> b -> s -> t

ex6 :: Map String String
ex6 = benders & L.at "Missing" ?~ "New Entry"

ex7 :: (Maybe String, Maybe String)
ex7 = (1 :: Int, 2 :: Int) & both ?~ "twins!"

sans :: At m => Index m -> m -> m
sans k = at k  .~ Nothing

ex8 :: Map String String
ex8 = L.sans "Zuko" benders


