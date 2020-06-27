module  Closure
    (   Closure
    ,   closureVar
    ,   closureBody
    ,   closureEnv
    ,   mkClosure
    )   where

import Var
import Env
import Syntax

data Closure = Closure
    { cloVar :: Var
    , cloExp :: Expr
    , cloEnv :: Env
    }

instance Show Closure where
    show c =  "Closure { var = " 
           ++ show (cloVar c) 
           ++ ", env = " 
           ++ show (cloEnv c)
           ++ " }"

closureVar :: Closure -> Var
closureVar = cloVar

closureBody :: Closure -> Expr
closureBody = cloExp

closureEnv :: Closure -> Env
closureEnv = cloEnv

mkClosure :: Var -> Expr -> Env -> Closure
mkClosure x e env = Closure 
    { cloVar = x 
    , cloExp = e
    , cloEnv = env
    }
