{-# LANGUAGE LambdaCase     #-}

module  Env
    (   Env
    ,   newEnv
    ,   findAddr
    ,   bind
    )   where

import Var
import Addr

import Data.Map.Strict as M


newtype Env = Env { unEnv :: Map Var Addr }

instance Show Env where
    show = show . M.toList . unEnv

newEnv :: Env
newEnv = Env mempty


findAddr :: Env -> Var  -> Addr
findAddr env var = case M.lookup var (unEnv env) of
    Just addr  -> addr
    Nothing -> error $ "Variable unbound:" ++ show var

-- Add binding to existing environment
bind :: Var -> Addr -> Env -> Env
bind x addr env = Env $ insert x addr (unEnv env)
