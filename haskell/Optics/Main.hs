module  Main
    (   main
    ,   Nat     (..)
    ,   SBool   (..)
    ,   Leq     (..)
    ,   If 
    ,   Vec     (..)
    )   where

import Prelude      hiding (head)

import Optics.If
import Optics.Nat
import Optics.Leq
import Optics.Vec
import Optics.Bool


main :: IO ()
main = do
    return ()
