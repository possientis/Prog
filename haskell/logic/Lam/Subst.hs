{-# LANGUAGE LambdaCase         #-}

module  Lam.Subst
    (   subst_
    ,   subst
    )   where

import Lam.T

subst_ :: (Eq v) => (v -> T v) -> [v] -> T v -> T v 
subst_ f xs = \case
    Var x       -> if x `elem` xs then Var x else f x
    App t1 t2   -> App (subst_ f xs t1) (subst_ f xs t2)
    Lam x t1    -> Lam x (subst_ f (x : xs) t1)


subst :: (Eq v) => (v -> T v) -> T v -> T v
subst f = subst_ f []

