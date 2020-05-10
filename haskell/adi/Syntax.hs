{-# LANGUAGE DeriveFunctor      #-}

module  Syntax  
    (   ExprF   (..)
    ,   Expr
    ,   eVar
    ,   eNum
    )   where

import Data.Functor.Foldable

import Op
import Var

data ExprF a
    = EVar Var
    | ENum Integer
    | EOp  Op a a
    | EIf  a a a
    | EApp a a
--    | ERec Var a
    | ELam Var a
    deriving (Functor)

type Expr = Fix ExprF

eVar :: String -> Expr
eVar s = Fix $ EVar $ mkVar s

eNum :: Integer -> Expr
eNum n = Fix $ ENum n
