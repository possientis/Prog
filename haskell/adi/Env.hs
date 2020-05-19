{-# LANGUAGE LambdaCase     #-}

module  Env
    (   Env
    ,   Value
    ,   Closure
    ,   newEnv
    ,   find
    ,   mkVal
    ,   mkClosure
    ,   val
    ,   closure
    ,   bind
    ,   evalClosure
    )   where

import Data.Map.Strict as M

import Var

newtype Env = Env { unEnv :: Map Var Value }

instance Show Env where
    show = show . M.toList . unEnv

data Value 
    = Val Integer
    | Clo Closure

instance Show Value where
    show = \case 
        Val n   -> show n
        Clo c   -> show c

data Closure = Closure
    { cloVar :: Var
    , cloFun :: Env -> Value 
    , cloEnv :: Env
    }

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

mkClosure :: Var -> (Env -> Value) -> Env -> Value
mkClosure x v e = Clo $ Closure 
    { cloVar = x 
    , cloFun = v
    , cloEnv = e
    }

val :: Value -> Maybe Integer
val = \case
    Val n   -> Just n
    Clo _   -> Nothing

closure :: Value -> Maybe Closure
closure = \case
    Val _   -> Nothing
    Clo c   -> Just c

-- Given a value to which the closure variable is bound, 
-- returns the value corresponding to the closure evaluation.
-- This is simply the value returned by the closure function
-- evaluated at the closure 'local environment', defined as
-- the closure environment with the additional binding of
-- the closure variable to the value argument.
evalClosure :: Closure -> Value -> Value
evalClosure c v = (cloFun c) (bind (cloVar c) v (cloEnv c))
