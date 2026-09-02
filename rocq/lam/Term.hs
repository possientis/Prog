module  Term
    (   P (..)
    )   where

data P v
    = Var v
    | App (P v) (P v)
    | Lam v (P v)


instance Functor P where
    fmap f (Var x)      = Var (f x)
    fmap f (App t1 t2)  = App (fmap f t1) (fmap f t2)
    fmap f (Lam x t1)   = Lam (f x) (fmap f t1)
