{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE DeriveFunctor      #-}

module  Syntax  
    (   ExprF   (..)
    ,   Expr
    ,   eVar
    ,   eNum
    ,   eOp
    ,   eIf
    ,   eLam
    ,   eApp
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
--    | ERec Var a
    deriving (Functor)

type Expr = Fix ExprF

eVar :: String -> Expr
eVar s = Fix $ EVar $ mkVar s

eNum :: Integer -> Expr
eNum n = Fix $ ENum n

eOp :: Op -> Expr -> Expr -> Expr
eOp op e1 e2 = Fix $ EOp op e1 e2 

eIf :: Expr -> Expr -> Expr -> Expr
eIf ez e1 e2 = Fix $ EIf ez e1 e2

eLam :: Var -> Expr -> Expr
eLam x e = Fix $ ELam x e

eApp :: Expr -> Expr -> Expr
eApp e1 e2 = Fix $ EApp e1 e2

toNum :: Expr -> Maybe Integer
toNum = cata $ \case
    ENum n  -> Just n
    _       -> Nothing 




