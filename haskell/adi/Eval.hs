{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval
    (   Eval    (..)    -- TODO: hide 
    ,   find
    ,   askEnv
    )   where

import Env
import Addr
import Heap
import State
import Value

import Data.Functor.Identity
import Control.Monad.Trans.State hiding (State)

newtype Eval a = Eval { unEval :: StateT State Identity a } 
    deriving (Functor, Applicative, Monad)

askEnv :: Eval Env
askEnv  = Eval $ getEnv <$> get

find :: Addr -> Eval Value
find addr = Eval $ do
    heap <- getHeap <$> get
    return $ findVal heap addr 

