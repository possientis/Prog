{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ConstraintKinds        #-}

module  Eval
    (   Eval 
    ,   askEnv
    ,   find
    ,   alloc
    ,   write
    ,   localEnv
    )   where

import Env
import Log
import Addr
import Heap
import Value

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

type Eval m
    = ( MonadReader Env m
      , MonadWriter Log m
      , MonadState Heap m 
      )

-- Returns current environment
askEnv :: (MonadReader Env m) => m Env
askEnv  = ask

-- Retrieves value stored in the Heap at given memory address
find :: (MonadState Heap m) => Addr -> m Value
find addr = findVal addr <$> get

-- Allocates new memory address
alloc :: (MonadState Heap m) => m Addr
alloc = do
    (heap,addr) <- heapAlloc <$> get
    put heap
    return addr

-- Write a value at a given memory address
write 
    :: (MonadState Heap m, MonadWriter Log m) 
    => Addr 
    -> Value 
    -> m ()
write addr v = do
    heap <- heapWrite addr v <$> get
    put heap
    tell ["write at address " ++ show addr ++ ": " ++ show v]

-- Run computation in a local environment
localEnv 
    :: (MonadReader Env m) 
    => Env 
    -> m Value 
    -> m Value
localEnv env ev = local (const env) ev
