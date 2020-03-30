module  Traversal
    (   ex1, ex2, ex3
    )   where

import Control.Lens

ex1 :: [String]
ex1 = ("Bubbles","Buttercup") ^.. both

ex2 :: (String, String)
ex2 = over both (++ "!") ("Bubbles","Buttercup")

ex3 :: (String, String)
ex3 = ("Bubbles","Buttercup") & both %~ (++ "!")
