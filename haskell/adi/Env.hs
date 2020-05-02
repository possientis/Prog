module  Env
    (   Env
    ,   newEnv
    )   where


import Data.Map

import Var

newtype Env = Env { _unEnv :: Map Var Integer }

newEnv :: Env
newEnv = Env mempty
