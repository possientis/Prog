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
    Fix (ENum n)    -> reduceNum n
    Fix (EBool b)   -> reduceBool b
    Fix (EVar x)    -> reduceVar x
    Fix (EOp op es) -> reduceOp op es
    _               -> error "xxx"

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

-- Arguments are irreducible
reduceOp_ :: Op -> [Expr] -> Expr
reduceOp_  op es
    | op == oAdd = let [Fix(ENum n1), Fix(ENum n2)] = es in eNum (n1 + n2)
    | otherwise  = undefined

