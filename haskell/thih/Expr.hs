module  Expr
    (   Expr        (..)
    ,   BindGroup   (..)
    ,   tiExpr
    )   where

import TI
import Infer
import Syntax
import Literal
import TypeClass
import BindGroup
import Assumption

data Expr 
    = Var Id
    | Lit Literal
    | Const Assump          -- named constants
    | Ap Expr Expr
    | Let BindGroup Expr


tiExpr :: Infer Expr Type
tiExpr _ _ (Lit l) = tiLit l

tiExpr _ as (Var i) = do
    sc         <- find i as 
    (ps :=> t) <- freshInst sc
    return (ps,t)

tiExpr _ _ (Const (_:>:sc)) = do
    (ps :=> t) <- freshInst sc
    return (ps,t)

tiExpr ce as (Ap e f) = do
    (ps, te) <- tiExpr ce as e
    (qs, tf) <- tiExpr ce as f
    t        <- newTVar Star
    unify (tf `fn` t) te
    return (ps ++ qs, t)

tiExpr ce as (Let bg e) = do
    (ps, as') <- tiBindGroup ce as bg
    (qs, t)   <- tiExpr ce (as' ++ as) e
    return (ps ++ qs, t)

