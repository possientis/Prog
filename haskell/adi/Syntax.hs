{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}

module  Syntax  
    (   ExprF   (..)
    ,   Expr
    ,   eNum
    ,   eBool
    ,   eVar
    ,   eOp
    ,   eIf
    ,   eLam
    ,   eApp
    ,   eRec
    )   where

import Data.Functor.Foldable

import Op
import Var

data ExprF a
    = ENum  Integer
    | EBool Bool
    | EVar  Var
    | EOp   Op [a]
    | EIf   a a a
    | ELam  Var a
    | EApp  a a
    | ERec  Var a
    deriving (Functor)

type Expr = Fix ExprF

eNum :: Integer -> Expr
eNum n = Fix $ ENum n

eBool :: Bool -> Expr
eBool b = Fix $ EBool b

eVar :: String -> Expr
eVar s = Fix $ EVar $ mkVar s

eOp :: Op -> [Expr] -> Expr
eOp op es = Fix $ EOp op es

eIf :: Expr -> Expr -> Expr -> Expr
eIf ez e1 e2 = Fix $ EIf ez e1 e2

eLam :: String -> Expr -> Expr
eLam x e = Fix $ ELam (mkVar x) e

eApp :: Expr -> Expr -> Expr
eApp e1 e2 = Fix $ EApp e1 e2

eRec :: String -> Expr -> Expr
eRec f e = Fix $ ERec (mkVar f) e
