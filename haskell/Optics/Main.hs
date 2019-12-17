module  Main
    (   main
    ,   If 
    ,   Plus
    ,   IsEven
    ,   Nat     (..)
    ,   Fin     (..)
    ,   SBool   (..)
    ,   Leq     (..)
    ,   Vec     (..)
    ,   Lens    (..)
    ,   Prism   (..)
    ,   Adapter (..)
    ,   FunList (..)
    )   where

import Prelude      hiding (head)

import Optics.If
import Optics.Nat
import Optics.Fin
import Optics.Leq
import Optics.Vec
import Optics.Lens
import Optics.Bool
import Optics.Plus
import Optics.Prism
import Optics.FinVec
import Optics.IsEven
import Optics.FunList
import Optics.Adapter


main :: IO ()
main = do
    print check0
    print check1
    print check2
    print check3
