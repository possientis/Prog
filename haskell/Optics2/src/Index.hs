module  Index
    (   ex0, ex1, ex2, ex3
    )   where

import Data.Map as M
import Data.Monoid

kings :: [String]
kings  = ["Henry I", "Henry II", "Henry III"]

ex0 :: String
ex0 = kings !! 0

ex1 :: String
ex1 = kings !! 1

ex2 :: String
ex2 = kings !! 2

ex3 :: String
ex3 = kings !! 3    -- error


turtles :: Map String String
turtles = M.fromList [("Leo","Katanas"),("Raph","Sai")]

ex4 :: Maybe String
ex4 = M.lookup "Leo" turtles

ex5 :: Map String String
ex5 = M.adjust ("Two " <>) "Leo" turtles    -- adjust value, not key
