{-# LANGUAGE DataKinds  #-}

import Prelude hiding ((+))

import Modular
import Field

x :: Mod 13
x =  Mod 6

y :: Mod 13
y =  Mod 7

main :: IO ()
main = do
    print $ x + y

