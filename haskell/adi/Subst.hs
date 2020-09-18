{-# LANGUAGE LambdaCase             #-}

module  Subst 
    (   subst_
    ,   subst
    ,   (<-:)
    )   where

import Data.Functor.Foldable

import Op
import Var
import Syntax

subst_ :: (Var -> Expr) -> [Var] -> Expr -> Expr
subst_ f xs = \case
    Fix (ENum n)            -> substNum n
    Fix (EBool b)           -> substBool b
    Fix (EVar x)            -> substVar f xs x
    Fix (EOp op es)         -> substOp f xs op es
    Fix (EIf e e1 e2)       -> substIf f xs e e1 e2 
    Fix (ELam x e1)         -> substLam f xs x e1
    Fix (EApp e1 e2)        -> substApp f xs e1 e2
    Fix (ERec x e1)         -> substRec f xs x e1
    Fix (EZero)             -> substZero
    Fix (ESuc e1)           -> substSuc f xs e1
    Fix (ECase e e1 x e2)   -> substCase f xs e e1 x e2

subst :: (Var -> Expr) -> Expr -> Expr
subst f = subst_ f []

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

substApp :: (Var -> Expr) -> [Var] -> Expr -> Expr -> Expr
substApp f xs e1 e2 = eApp (subst_ f xs e1) (subst_ f xs e2)

substRec :: (Var -> Expr) -> [Var] -> Var -> Expr -> Expr
substRec f xs x e1 = Fix (ERec x (subst_ f (x : xs) e1))

substZero :: Expr
substZero = eZero

substSuc :: (Var -> Expr) -> [Var] -> Expr -> Expr
substSuc f xs e1 = eSuc (subst_ f xs e1)

substCase :: (Var -> Expr) -> [Var] -> Expr -> Expr -> Var -> Expr -> Expr
substCase f xs e e1 x e2 
    = Fix (ECase (subst_ f xs e) (subst_ f xs e1) x (subst_ f (x : xs) e2))


(<-:) :: Expr -> Var  -> (Var -> Expr)
(<-:) t x y = if y == x then t else Fix (EVar y)
