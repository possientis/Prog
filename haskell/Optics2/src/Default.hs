module  Default
    (
    )   where

import Control.Lens

-- non :: Eq a => a -> Iso' (Maybe a) a

-- non :: Eq a => a -> Traversal' (Maybe a) a


ex1 :: Int
ex1 = Nothing ^. non 0 

ex2 :: String
ex2 = Nothing ^. non "default"

ex3 :: String
ex3 = Just "value" ^. non "default"
