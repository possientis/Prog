module  Optics.Test.FunList
    (   specFunList
    ,   FunList
    , t1 
    , t2
    , t3
    , t4
    , t5
    )   where

import Test.Hspec
import Optics.FunList

specFunList :: Spec
specFunList = describe "Testing FunList..." $ do
    it "Checked module compiled" $
        True `shouldBe` True


type T t = FunList Int Bool t

t1 :: T String
t1 = Done "hello"

t2 :: T (Bool -> String)
t2 = Done show

t3 :: T String
t3 = More 0 t2

t4 :: T (Bool -> Bool -> String)
t4 = Done (\x y -> show x ++ ":" ++ show y)

t5 :: T String
t5 = More 1 (More 0 t4)
