{-# LANGUAGE DeriveFunctor      #-}

module  Syntax  
    (   ExprF   (..)
    ,   Expr
    ,   eval
    )   where

import Data.Functor.Foldable

import Op
import Var
import Env

data ExprF a
    = EVar Var
    | ENum Integer
    | EBin Op a a
    | EIf  a a a
    | EApp a a
    | ERec Var a
    | ELam Var a
    deriving (Functor)

type Expr = Fix ExprF

eval :: Env -> Expr -> Integer
eval _env = cata undefined
