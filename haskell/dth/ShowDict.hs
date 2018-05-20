{-# LANGUAGE ScopedTypeVariables #-}

import Data.Map

data ShowDict a = ShowDict { showMethod :: a -> String }


showBool :: Bool -> String
showBool True = "True"
showBool False = "False"

showDictBool :: ShowDict Bool
showDictBool = ShowDict showBool



class A a where
    xA :: a -> String
    yA :: a -> a 
    zA :: Int -> a


data B a = B
    { xB :: a -> String
    , yB :: a -> a
    , zB :: Int -> a
    }
     
instance A Int where
    xA = show
    yA = id
    zA = id


impOnInt :: B Int 
impOnInt = B
    { xB = show
    , yB = id
    , zB = id
    }

data Proxy a = Proxy

test :: forall a. (A a) => Proxy a -> Int -> String
test _ = (xA :: a -> String) . yA . zA

test' :: B a -> Int -> String
test' imp = (xB imp) . (yB imp) . (zB imp) 


ex1 :: String
ex1 = test (Proxy :: Proxy Int) 34

ex2 :: String
ex2 = test' impOnInt 34



