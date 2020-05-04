module  Env
    (   Env
    ,   newEnv
    ,   find
    )   where


import Data.Map as M

import Var

newtype Env = Env { unEnv :: Map Var Integer }

newEnv :: Env
newEnv = Env mempty

find :: Env -> Var -> Integer
find env var = case M.lookup var (unEnv env) of
    Just n  -> n
    Nothing -> error $ "Variable unbound:" ++ show var
