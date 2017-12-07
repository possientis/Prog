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
 
 -- TODO


