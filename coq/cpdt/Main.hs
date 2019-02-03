{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where
    
import Test.Hspec
import Haskell.Typed 

main :: IO ()
main = hspec $ do
    describe "Checking Haskell.Typed" $
        sequence_ tests

tests :: [Spec]
tests  = [ test1
         , test2
         , test3
         , test4
         , test5
         , test6
         , test7
         , test8
         , test9
         , test10
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

test1 :: Spec
test1 =  it "Testing expression 1" $ do
    eval exp1 `shouldBe` 42 

test2 :: Spec
test2 =  it "Testing expression 2" $ do
    eval exp2 `shouldBe` True

test3 :: Spec
test3 =  it "Testing expression 3" $ do
    eval exp3 `shouldBe` False

test4 :: Spec
test4 =  it "Testing expression 4" $ do
    eval exp4 `shouldBe` 35

test5 :: Spec
test5 =  it "Testing expression 5" $ do
    eval exp5 `shouldBe` False

test6 :: Spec
test6 =  it "Testing expression 6" $ do
    eval exp6 `shouldBe` True

test7 :: Spec
test7 =  it "Testing expression 7" $ do
    eval exp7 `shouldBe` True

test8 :: Spec
test8 =  it "Testing expression 8" $ do
    eval exp8 `shouldBe` False

test9 :: Spec
test9 =  it "Testing expression 9" $ do
    eval exp9 `shouldBe` False

test10 :: Spec
test10 =  it "Testing expression 10" $ do
    eval exp10 `shouldBe` True

{- TypeDenote t is not an instance of Eq
test :: (Exp t, TypeDenote t, Int) -> Spec
test (e,v,n) = it ("Testing expresion  " ++ show n) $ do
    eval e `shouldBe` v  
-}



