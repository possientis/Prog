{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval
    (   Eval    (..)    -- TODO: hide 
    ,   alloc
    ,   askEnv
    ,   find
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
askEnv  = Eval $ gets getEnv 

find :: Addr -> Eval Value
find addr = Eval $ do
    heap <- gets getHeap
    return $ findVal heap addr 

alloc :: Eval Addr
alloc = Eval $ do
    s <- get
    let heap = getHeap s
    let (heap',addr) = heapAlloc heap
    let s' = setHeap heap' s
    put s'
    return addr
