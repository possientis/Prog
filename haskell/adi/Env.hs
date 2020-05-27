{-# LANGUAGE LambdaCase     #-}

module  Env
    (   Env
    ,   Value
    ,   Closure
    ,   newEnv
    ,   find
    ,   mkVal
    ,   mkClosure
    ,   mkExpr
    ,   val
    ,   closure
    ,   expr
    ,   closureVar
    ,   closureBody
    ,   closureEnv
    ,   bind
    )   where

import Data.Map.Strict as M

import Var
import Syntax

newtype Env = Env { unEnv :: Map Var Value }

instance Show Env where
    show = show . M.toList . unEnv

data Value 
    = Val Integer
    | Clo Closure
    | Exp Expr

instance Show Value where
    show = \case 
        Val n   -> show n
        Clo c   -> show c
        Exp _   -> "<expression>"

data Closure = Closure
    { cloVar :: Var
    , cloExp :: Expr
    , cloEnv :: Env
    }

closureVar :: Closure -> Var
closureVar = cloVar

closureBody :: Closure -> Expr
closureBody = cloExp

closureEnv :: Closure -> Env
closureEnv = cloEnv

instance Show Closure where
    show c =  "Closure { var = " 
           ++ show (cloVar c) 
           ++ ", env = " 
           ++ show (cloEnv c)

newEnv :: Env
newEnv = Env mempty

find :: Var -> Env -> Value
find var env = case M.lookup var (unEnv env) of
    Just v  -> v
    Nothing -> error $ "Variable unbound:" ++ show var

-- Add binding to existing environment
bind :: Var -> Value -> Env -> Env
bind x v env = Env $ insert x v (unEnv env)

mkVal :: Integer -> Value
mkVal = Val

mkClosure :: Var -> Expr -> Env -> Value
mkClosure x e env = Clo $ Closure 
    { cloVar = x 
    , cloExp = e
    , cloEnv = env
    }

mkExpr :: Expr -> Value
mkExpr = Exp

val :: Value -> Maybe Integer
val = \case
    Val n   -> Just n
    _       -> Nothing

closure :: Value -> Maybe Closure
closure = \case
    Clo c   -> Just c
    _       -> Nothing

expr :: Value -> Maybe Expr
expr = \case
    Exp e   -> Just e
    _       -> Nothing
