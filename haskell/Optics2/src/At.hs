{-# LANGUAGE RankNTypes         #-}

module  At
    (   ex1, ex2
    ,   At  (..)
    )   where

import Data.Map
import Control.Lens hiding (At (..))

turtles :: Map String String
turtles = fromList [("Leo","Katanas"),("Raph","Sai")]

ex1 :: Map String String
ex1 = insert "Mikey" "Nunchaku" turtles

ex2 :: Map String String
ex2 = delete "Leo" turtles

class At m where 
    at :: Index m -> Lens' m (Maybe (IxValue m))



