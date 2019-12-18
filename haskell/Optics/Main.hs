module  Main
    (   main
    )   where


import Test.Hspec
import Optics.Test.Main


main :: IO ()
main = hspec $ do
    specMain
