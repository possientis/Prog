module  Syntax
    (   Term
    ,   var 
    ,   lam
    ,   app
    )   where

import Test.QuickCheck

import Variable (Var) 

var :: Var -> Term
var  = Var

lam :: Var -> Term -> Term
lam = Lam

app :: Term -> Term -> Term 
app = App

type Term = Term_ Var

data Term_ a
    = Var a
    | Lam a (Term_ a)
    | App (Term_ a) (Term_ a)

-- TODO : proper parsing and pretty printing 
instance (Show  a) => Show (Term_ a) where
    show (Var v)    = show v
    show (Lam v t)  = "(\\" ++ show v ++ " -> " ++ show t ++ ")"
    show (App t s)  = "("   ++ show t ++ " "    ++ show s ++ ")"

-- TODO : something better than this
instance (Arbitrary a) => Arbitrary (Term_ a) where
    arbitrary = frequency 
        [ (1, Var <$> arbitrary)
        , (1, Lam <$> arbitrary <*> arbitrary)
        , (1, App <$> arbitrary <*> arbitrary)
        ]

