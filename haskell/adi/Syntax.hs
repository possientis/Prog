{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}

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
    ,   eCase
    )   where

import Data.Functor.Classes
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

instance Eq1 ExprF where
    liftEq _ (ENum n)           (ENum m)            = n == m
    liftEq _ (EBool x)          (EBool y)           = x == y
    liftEq _ (EVar x)           (EVar y)            = x == y
    liftEq f (EOp op1 xs)       (EOp op2 ys)        = eqOp   f op1 op2 xs ys
    liftEq f (EIf e1 f1 g1)     (EIf e2 f2 g2)      = eqIf   f e1 e2 f1 f2 g1 g2
    liftEq f (ELam x e1)        (ELam y e2)         = eqLam  f x y e1 e2
    liftEq f (EApp e1 f1)       (EApp e2 f2)        = eqApp  f e1 e2 f1 f2
    liftEq f (ERec x e1)        (ERec y e2)         = eqRec  f x y e1 e2
    liftEq _ (EZero)            (EZero)             = True 
    liftEq f (ESuc e1)          (ESuc e2)           = f e1 e2
    liftEq f (ECase e1 f1 x g1) (ECase e2 f2 y g2)  = eqCase f x y e1 e2 f1 f2 g1 g2
    liftEq _ _                  _                   = False 

eqOp :: (a -> b -> Bool) -> Op -> Op -> [a] -> [b] -> Bool
eqOp f op1 op2 xs ys 
    =  (op1 == op2)
    && (length xs == length ys)
    && (and $ map (uncurry f) $ zip xs ys)

eqIf :: (a -> b -> Bool) -> a -> b -> a -> b -> a -> b -> Bool
eqIf f e1 e2 f1 f2 g1 g2 = f e1 e2 && f f1 f2 && f g1 g2

eqLam :: (a -> b -> Bool) -> Var -> Var -> a -> b -> Bool
eqLam f x y e1 e2 = x == y && f e1 e2

eqApp :: (a -> b -> Bool) -> a -> b -> a -> b -> Bool
eqApp f e1 e2 f1 f2 = f e1 e2 && f f1 f2

eqRec :: (a -> b -> Bool) -> Var -> Var -> a -> b -> Bool
eqRec f x y e1 e2 = x == y && f e1 e2

eqCase :: (a -> b -> Bool) -> Var -> Var -> a -> b -> a -> b -> a -> b -> Bool
eqCase f x y e1 e2 f1 f2 g1 g2 = x == y && f e1 e2 && f f1 f2 && f g1 g2

eNum :: Integer -> Expr
eNum n = Fix $ ENum n

eBool :: Bool -> Expr
eBool b = Fix $ EBool b

eVar :: String -> Expr
eVar s = Fix $ EVar $ mkVar s

eOp :: Op -> [Expr] -> Expr
eOp op es = Fix $ EOp op es

eIf :: Expr -> Expr -> Expr -> Expr
eIf b e1 e2 = Fix $ EIf b e1 e2

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
