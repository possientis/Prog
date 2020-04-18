module  Tree
    (   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8
    )   where


import Data.Tree
import Control.Lens

tree :: Tree Int
tree = Node 1 [ Node 2 [ Node 4 [] ]
              , Node 3 [ Node 5 [], Node 6 []]]

ex1 :: Maybe Int
ex1 = tree ^? ix []

ex2 :: Maybe Int
ex2 = tree ^? ix [0]

ex4 :: Maybe Int
ex4 = tree ^? ix [0,0]

ex3 :: Maybe Int
ex3 = tree ^? ix [1]

ex5 :: Maybe Int
ex5 = tree ^? ix [1,0]

ex6 :: Maybe Int
ex6 = tree ^? ix [1,1]

ex7 :: Maybe Int
ex7 = tree ^? ix [6,4]


ex8 :: Maybe String
ex8 = reverse ^? ix "Stella!"

ex9 :: String -> String
ex9 = reverse & ix "password" .~ "You found the secret!"
