{-# LANGUAGE LambdaCase     #-}

module  Env
    (   Env
    ,   newEnv
    ,   findAddr
    ,   bind
    )   where

import Var
import Addr
import Error

import Data.Map.Strict as M

newtype Env = Env { unEnv :: Map Var Addr }

instance Show Env where
    show = show . M.toList . unEnv

newEnv :: Env
newEnv = Env mempty

findAddr :: Env -> Var  -> Either Error Addr
findAddr env var = case M.lookup var (unEnv env) of
    Nothing -> Left $ errorFindAddr env var
    Just addr  -> Right addr

-- Add binding to existing environment
bind :: Var -> Addr -> Env -> Env
bind x addr env = Env $ insert x addr (unEnv env)

errorFindAddr :: Env -> Var -> Error
errorFindAddr env var = mkError $ unlines
    [ "findAddr: unbound variable "
    ++ show var
    , "The current environment is as follows:"
    , show env
    ] 
