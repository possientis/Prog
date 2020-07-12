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
    ,   eZero
    ,   eSuc
    ,   eNat
    ,   eCase
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
    | EZero             -- inductive type Nat
    | ESuc a            -- successor for Nat
    | ECase a a Var a   -- ECase e e1 x e2 : e == zero -> e1 , e == suc x -> e2
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

eZero :: Expr
eZero = Fix $ EZero

eSuc :: Expr -> Expr
eSuc e1 = Fix $ ESuc e1

eCase :: Expr -> Expr -> String -> Expr -> Expr
eCase e e1 x e2 = Fix $ ECase e e1 (mkVar x) e2 

eNat :: Integer -> Expr
eNat n
    | n > 0   = eSuc $ eNat (n - 1)
    | n == 0  = eZero
    | otherwise = error "eNat: negative argument"
