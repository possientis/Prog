{-# LANGUAGE LambdaCase             #-}

module  Reduce
    (   irreducible
    ,   reduce
    )   where 

import Data.Functor.Foldable

import Op
import Var
import Syntax

irreducible :: Expr -> Bool
irreducible = \case
    Fix (ENum _)    -> True
    Fix (EBool _)   -> True
    Fix (EZero)     -> True
    Fix (ESuc e)    -> irreducible e
    Fix (ELam _ _)  -> True
    _               -> False

reduce :: Expr -> Expr
reduce = \case
    Fix (ENum n)        -> reduceNum n
    Fix (EBool b)       -> reduceBool b
    Fix (EVar x)        -> reduceVar x
    Fix (EOp op es)     -> reduceOp op es
    Fix (EIf e e1 e2)   -> reduceIf e e1 e2
    Fix (ELam x e1)     -> reduceLam x e1
    Fix (EApp e1 e2)    -> reduceApp e1 e2
    _                   -> error "xxx"

reduceNum :: Integer -> Expr
reduceNum = eNum

reduceBool :: Bool -> Expr
reduceBool = eBool

reduceVar :: Var -> Expr
reduceVar _ = error "reduceVar: should never be called"

reduceOp :: Op -> [Expr] -> Expr
reduceOp op es = case es of
    []      -> reduceOp_ op es 
    [x]     -> if irreducible x then reduceOp_ op es else eOp op [reduce x]
    [x,y]   -> 
        if irreducible x
            then if irreducible y
                then reduceOp_ op es
                else eOp op [x,reduce y]
            else eOp op [reduce x, y]
    _       -> error "reduceOp: unexpected primitive call with 3 arguments"

reduceIf :: Expr -> Expr -> Expr -> Expr
reduceIf e e1 e2 = if irreducible e
    then let Fix (EBool b) = e in if b then e1  else e2
    else eIf (reduce e) e1 e2

reduceLam :: Var -> Expr -> Expr
reduceLam x e1 = Fix (ELam x e1)

reduceApp :: Expr -> Expr -> Expr
reduceApp _e1 _e2 = undefined

-- Arguments are irreducible
reduceOp_ :: Op -> [Expr] -> Expr
reduceOp_  op es
    | op == oAdd = let [Fix(ENum n1), Fix(ENum n2)] = es in eNum (n1 + n2)
    | op == oMul = let [Fix(ENum n1), Fix(ENum n2)] = es in eNum (n1 * n2)
    | op == oSub = let [Fix(ENum n1), Fix(ENum n2)] = es in eNum (n1 - n2)
    | op == oDiv = let [Fix(ENum n1), Fix(ENum n2)] = es in eNum (n1 `div` n2)
    | op == oAnd = let [Fix(EBool b1), Fix(EBool b2)] = es in eBool (b1 && b2)
    | op == oOr  = let [Fix(EBool b1), Fix(EBool b2)] = es in eBool (b1 || b2)
    | op == oImp = let [Fix(EBool b1), Fix(EBool b2)] = es in eBool (imp b1 b2)
    | op == oNot = let [Fix(EBool b1)]                = es in eBool (not b1)
    | op == oLe  = let [Fix(ENum n1), Fix(ENum n2)] = es in eBool (n1 <= n2)
    | op == oEq  = let [Fix(ENum n1), Fix(ENum n2)] = es in eBool (n1 == n2)
    | otherwise  = undefined
    where
        imp :: Bool -> Bool -> Bool
        imp b1 b2 = not b1 || b2
