{-# LANGUAGE LambdaCase             #-}

module  Subst 
    (   subst_
    )   where

import Data.Functor.Foldable

import Op
import Var
import Syntax

subst_ :: (Var -> Expr) -> [Var] -> Expr -> Expr
subst_ f xs = \case
    Fix (ENum n)        -> substNum n
    Fix (EBool b)       -> substBool b
    Fix (EVar x)        -> substVar f xs x
    Fix (EOp op es)     -> substOp f xs op es
    Fix (EIf e e1 e2)   -> substIf f xs e e1 e2 
    Fix (ELam x e1)     -> substLam f xs x e1
    _                   -> undefined 

substNum :: Integer -> Expr
substNum = eNum

substBool :: Bool -> Expr
substBool = eBool

substVar :: (Var -> Expr) -> [Var] -> Var -> Expr
substVar f xs x = if x `elem` xs
    then Fix (EVar x)   -- x is deemed bound, no substitution 
    else f x            -- x is deemed free, substituted with (f x)

substOp :: (Var -> Expr) -> [Var] -> Op -> [Expr] -> Expr
substOp f xs op = eOp op . map (subst_ f xs)

substIf :: (Var -> Expr) -> [Var] -> Expr -> Expr -> Expr -> Expr
substIf f xs e e1 e2 = eIf (subst_ f xs e) (subst_ f xs e1) (subst_ f xs e2)

substLam :: (Var -> Expr) -> [Var] -> Var -> Expr -> Expr
substLam f xs x e1 = Fix (ELam x (subst_ f (x : xs) e1))
