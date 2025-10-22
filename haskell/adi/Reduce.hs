{-# LANGUAGE LambdaCase             #-}

module  Reduce
    (   irreducible
    ,   reduce
    ,   eval
    ,   trace
    )   where 

import Data.Fix

import Op
import Var
import DSL
import Subst
import Syntax

trace :: Expr -> [Expr]
trace e = if irreducible e
    then [e]
    else e : trace (reduce e)

eval :: Expr -> Expr
eval e = if irreducible e
    then e
    else eval (reduce e)

irreducible :: Expr -> Bool
irreducible = \case
    Fix (ENum _)    -> True
    Fix (EBool _)   -> True
    Fix (ELam _ _)  -> True
    Fix (EZero)     -> True
    Fix (ESuc e)    -> irreducible e
    _               -> False

reduce :: Expr -> Expr
reduce = \case
    Fix (ENum n)            -> reduceNum n
    Fix (EBool b)           -> reduceBool b
    Fix (EVar x)            -> reduceVar x
    Fix (EOp op es)         -> reduceOp op es
    Fix (EIf e e1 e2)       -> reduceIf e e1 e2
    Fix (ELam x e1)         -> reduceLam x e1
    Fix (EApp e1 e2)        -> reduceApp e1 e2
    Fix (ERec x e1)         -> reduceRec x e1
    Fix (EZero)             -> reduceZero
    Fix (ESuc e1)           -> reduceSuc e1
    Fix (ECase e e1 x e2)   -> reduceCase e e1 x e2

reduceNum :: Integer -> Expr
reduceNum = error "reduce: attempting to reduce an ENum"

reduceBool :: Bool -> Expr
reduceBool = error "reduce: attempting to reduce an EBool"

-- Yet a Var is not classified as irreducible
reduceVar :: Var -> Expr
reduceVar _ = error "reduce: attempting to reduce a Var"

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
reduceIf e e1 e2 
  | irreducible e , Fix (EBool b) <- e 
    = if b then e1  else e2  
  | irreducible e 
    = error "reduceIf: illegal argument"
  | otherwise 
    = eIf (reduce e) e1 e2

reduceLam :: Var -> Expr -> Expr
reduceLam = error "reduce: attempting to reduce a lambda abstraction"

reduceApp :: Expr -> Expr -> Expr
reduceApp e1 e2 
  | irreducible e1, irreducible e2, Fix (ELam x e) <- e1 
    = subst (e2 <-: x) e
  | irreducible e1, irreducible e2 
    = error "reduceApp: illegal arguments"
  | irreducible e1 
    = eApp e1 (reduce e2)
  | otherwise 
    = eApp (reduce e1) e2 

reduceRec :: Var -> Expr -> Expr
reduceRec x e1 = subst (Fix (ERec x e1) <-: x) e1


reduceZero :: Expr
reduceZero = error "reduce: attempting to reduce Zero"

reduceSuc :: Expr -> Expr
reduceSuc e1 = if irreducible e1
    then error "reduce: attempting to reduce successor of irreducible expression"
    else eSuc (reduce e1)


reduceCase :: Expr -> Expr -> Var -> Expr -> Expr
reduceCase e e1 x e2 = if irreducible e 
    then case e of
        Fix (EZero)     -> e1
        Fix (ESuc e3)   -> subst (e3 <-: x) e2
        _               -> error "reduce: case expression is not a Nat"
    else Fix (ECase (reduce e) e1 x e2)

-- Arguments are irreducible
reduceOp_ :: Op -> [Expr] -> Expr
reduceOp_  op es
    | op == oAdd, [Fix(ENum n1), Fix(ENum n2)] <- es = eNum (n1 + n2)
    | op == oMul, [Fix(ENum n1), Fix(ENum n2)] <- es = eNum (n1 * n2)
    | op == oSub, [Fix(ENum n1), Fix(ENum n2)] <- es = eNum (n1 - n2)
    | op == oDiv, [Fix(ENum n1), Fix(ENum n2)] <- es = eNum (n1 `div` n2)
    | op == oAnd, [Fix(EBool b1), Fix(EBool b2)] <- es = eBool (b1 && b2)
    | op == oOr , [Fix(EBool b1), Fix(EBool b2)] <- es = eBool (b1 || b2)
    | op == oImp, [Fix(EBool b1), Fix(EBool b2)] <- es = eBool (imp b1 b2)
    | op == oNot, [Fix(EBool b1)]                <- es = eBool (not b1)
    | op == oLe , [Fix(ENum n1), Fix(ENum n2)] <- es = eBool (n1 <= n2)
    | op == oEq , [Fix(ENum n1), Fix(ENum n2)] <- es = eBool (n1 == n2)
    | otherwise  = undefined
    where
        imp :: Bool -> Bool -> Bool
        imp b1 b2 = not b1 || b2
