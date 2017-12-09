{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Functor.Foldable

type Var = String

data Exp
    = Var Var
    | App Exp Exp
    | Lam [Var] Exp
    deriving Show


data ExpF a 
    = VarF Var
    | AppF a a
    | LamF [Var] a 
    deriving Functor

type instance Base Exp = ExpF
 
-- project is unknown :(
instance Foldable Exp where
    project (Var a) = VarF a
    project (App a b) = AppF a b
    project (Lam a b) = LamF a b

