{-# LANGUAGE TemplateHaskell    #-}

module  Banking
    (   Transaction
    ,   amount
    ,   transactions
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9
    ,   deposits1, deposits2, deposits3
    )   where

import Control.Lens
import Control.Applicative

data Transaction
    = Withdrawal { _amount :: Int }
    | Deposit    { _amount :: Int }
    deriving Show

makeLenses ''Transaction

newtype BankAccount = BankAccount
    { _transactions :: [Transaction]
    } deriving Show

makeLenses ''BankAccount
        

aliceAccount :: BankAccount
aliceAccount  = BankAccount [Deposit 100, Withdrawal 20, Withdrawal 10]

bobAccount :: BankAccount
bobAccount  = BankAccount [Deposit 10, Withdrawal 20, Deposit 30]

ex1 :: [Transaction]
ex1 = aliceAccount ^.. transactions . traversed


ex2 :: [Int]
ex2 = aliceAccount ^.. transactions . traversed . amount

deposits1 :: Traversal' [Transaction] Int
deposits1 = undefined

deposits2 :: Traversal [Transaction] [Transaction] Int Int
deposits2 = undefined

deposits3 
    :: (Applicative f) 
    => (Int -> f Int) 
    -> [Transaction] 
    -> f [Transaction]
deposits3 _ [] = pure []
deposits3 f (Withdrawal amt:ts) = liftA2(:)(pure $ Withdrawal amt) (deposits3 f ts)
deposits3 f (Deposit    amt:ts) = liftA2(:)(Deposit <$> f amt)(deposits3 f ts)  

ex3 :: [Int]
ex3 = aliceAccount ^.. transactions . deposits3

ex4 :: [Int]
ex4 = bobAccount ^.. transactions . deposits3

ex5 :: BankAccount
ex5 = bobAccount & transactions . deposits3 %~ (*10)

isDeposit :: Transaction -> Bool
isDeposit (Deposit _) = True
isDeposit _           = False

badDeposits :: Traversal' [Transaction] Int
badDeposits f ts = traverse go (filter isDeposit ts)
    where
        go (Deposit amt)    = Deposit <$> f amt
        go (Withdrawal _) = error "This shouldn't happen" 

ex6 :: [Int]
ex6 = bobAccount ^.. transactions . badDeposits -- looks good, but ...

ex7 :: BankAccount
ex7 = bobAccount & transactions . badDeposits *~ 10

deposits4 :: Traversal' [Transaction] Int 
deposits4 = traversed . filtered isDeposit . amount

ex8 :: [Int]
ex8 = bobAccount ^.. transactions . deposits4 

ex9 :: BankAccount
ex9 = bobAccount & transactions . deposits4 *~ 10


