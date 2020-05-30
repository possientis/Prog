{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}

module  Syntax  
    (   ExprF   (..)
    ,   Expr
    ,   eNum
    ,   eVar
    ,   eOp
    ,   eIf
    ,   eLam
    ,   eApp
    ,   eRec
    ,   toNum
    )   where

import Data.Functor.Foldable

import Op
import Var

data ExprF a
    = ENum Integer
    | EVar Var
    | EOp  Op a a
    | EIf  a a a
    | ELam Var a
    | EApp a a
    | ERec Var a
    deriving (Functor)

type Expr = Fix ExprF

eNum :: Integer -> Expr
eNum n = Fix $ ENum n

eVar :: String -> Expr
eVar s = Fix $ EVar $ mkVar s

eOp :: Op -> Expr -> Expr -> Expr
eOp op e1 e2 = Fix $ EOp op e1 e2 

eIf :: Expr -> Expr -> Expr -> Expr
eIf ez e1 e2 = Fix $ EIf ez e1 e2

eLam :: Var -> Expr -> Expr
eLam x e = Fix $ ELam x e

eApp :: Expr -> Expr -> Expr
eApp e1 e2 = Fix $ EApp e1 e2

eRec :: Var -> Expr -> Expr
eRec f e = Fix $ ERec f e

toNum :: Expr -> Maybe Integer
toNum = cata $ \case
    ENum n  -> Just n
    _       -> Nothing 

