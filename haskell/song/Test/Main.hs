module  Test.Main
    (   main
    )   where
import Test.Hspec
import Test.F13

main :: IO ()
main = hspec $ do
    specF13
