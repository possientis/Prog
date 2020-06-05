{-# LANGUAGE LambdaCase     #-}

module  Env
    (   Env
    ,   newEnv
    ,   find
    ,   bind
    )   where

import Data.Map.Strict as M

import Var
import Addr

newtype Env = Env { unEnv :: Map Var Addr }

instance Show Env where
    show = show . M.toList . unEnv

newEnv :: Env
newEnv = Env mempty


find :: Var -> Env -> Addr
find var env = case M.lookup var (unEnv env) of
    Just addr  -> addr
    Nothing -> error $ "Variable unbound:" ++ show var

-- Add binding to existing environment
bind :: Var -> Addr -> Env -> Env
bind x addr env = Env $ insert x addr (unEnv env)
