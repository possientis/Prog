{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}

module Main (main) where
    
import Test.Hspec
import Haskell.Typed 

main :: IO ()
main = hspec $ do
    describe "Checking Haskell.Typed" $
        sequence_ tests

tests :: [Spec]
tests  = map test $ zip items [1..10] 

data Item = 
    forall t. (Eq (TypeDenote t) , Show (TypeDenote t)) =>
    Item (Exp t, TypeDenote t)

items ::[Item]
items = [ item1
        , item2
        , item3
        , item4
        , item5
        , item6
        , item7
        , item8
        , item9
        , item10
        ] 

exp1  = NConst 42
exp2  = BConst True
exp3  = BConst False
exp4  = Binop Times (Binop Plus (NConst 2) (NConst 3)) (NConst 7)
exp5  = Binop EqN   (Binop Plus (NConst 2) (NConst 3)) (NConst 7)
exp6  = Binop EqN   (Binop Plus (NConst 2) (NConst 3)) (NConst 5)
exp7  = Binop EqB   (Binop EqN  (NConst 2) (NConst 2)) (BConst True)
exp8  = Binop EqB   (Binop EqN  (NConst 2) (NConst 3)) (BConst True)
exp9  = Binop Lt    (Binop Plus (NConst 2) (NConst 3)) (NConst 5)
exp10 = Binop Lt    (Binop Plus (NConst 2) (NConst 3)) (NConst 6)

item1  = Item (exp1,  42)
item2  = Item (exp2,  True)
item3  = Item (exp3,  False)
item4  = Item (exp4,  35)
item5  = Item (exp5,  False)
item6  = Item (exp6,  True)
item7  = Item (exp7,  True)
item8  = Item (exp8,  False)
item9  = Item (exp9,  False)
item10 = Item (exp10, True)


test :: (Item, Int) -> Spec
test (Item (e,v),n) = it ("Testing expresion  " ++ show n) $ do
    eval e `shouldBe` v  



