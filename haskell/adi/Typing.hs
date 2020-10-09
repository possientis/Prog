{-# LANGUAGE LambdaCase             #-}

module  Typing
    (   typeCheck 
    )   where

import Data.Functor.Foldable

import Op
import Var
import EType
import Syntax
import Context

typeCheck :: Context -> Expr -> Maybe EType
typeCheck ctx = \case
    Fix (ENum _)            -> Just TNum
    Fix (EBool _)           -> Just TBool
    Fix (EVar x)            -> typeCheckVar  ctx x
    Fix (EOp op es)         -> typeCheckOp   ctx op es
    Fix (EIf e e1 e2)       -> typeCheckIf   ctx e e1 e2
    Fix (ELam x e)          -> typeCheckLam  ctx x e
    Fix (EApp e1 e2)        -> typeCheckApp  ctx e1 e2
    Fix (ERec f e)          -> typeCheckRec  ctx f e
    Fix (EZero)             -> Just TNat
    Fix (ESuc e)            -> typeCheckSuc  ctx e
    Fix (ECase e e1 x e2)   -> typeCheckCase ctx e e1 x e2

typeCheckVar :: Context -> Var -> Maybe EType
typeCheckVar = (>>>)

typeCheckOp :: Context -> Op -> [Expr] -> Maybe EType 
typeCheckOp ctx op es
    | op == oAdd    = typeCheckNum  ctx es
    | op == oMul    = typeCheckNum  ctx es
    | op == oSub    = typeCheckNum  ctx es
    | op == oDiv    = typeCheckNum  ctx es
    | op == oAnd    = typeCheckBool ctx es
    | op == oOr     = typeCheckBool ctx es
    | op == oImp    = typeCheckBool ctx es
    | op == oNot    = typeCheckNot  ctx es
    | op == oLe     = typeCheckComp ctx es
    | op == oEq     = typeCheckComp ctx es
    | otherwise     = undefined

typeCheckIf :: Context -> Expr -> Expr -> Expr -> Maybe EType
typeCheckIf ctx e e1 e2 = do
    t  <- typeCheck ctx e
    t1 <- typeCheck ctx e1
    t2 <- typeCheck ctx e2
    if t == TBool && t1 == t2
        then Just t1
        else Nothing

typeCheckLam :: Context -> Var -> Expr -> Maybe EType
typeCheckLam _ctx _x _e1 = undefined

typeCheckApp :: Context -> Expr -> Expr -> Maybe EType
typeCheckApp = undefined

typeCheckRec :: Context -> Var -> Expr -> Maybe EType
typeCheckRec = undefined

typeCheckSuc :: Context -> Expr -> Maybe EType
typeCheckSuc = undefined

typeCheckCase :: Context -> Expr -> Expr -> Var -> Expr -> Maybe EType
typeCheckCase = undefined

typeCheckNum  :: Context -> [Expr] -> Maybe EType
typeCheckNum ctx es = do
    [e1,e2] <- Just es
    t1 <- typeCheck ctx e1
    t2 <- typeCheck ctx e2
    if t1 == TNum && t2 == TNum
        then Just TNum
        else Nothing

typeCheckBool  :: Context -> [Expr] -> Maybe EType
typeCheckBool ctx es = do
    [e1,e2] <- Just es
    t1 <- typeCheck ctx e1
    t2 <- typeCheck ctx e2
    if t1 == TBool && t2 == TBool
        then Just TBool
        else Nothing

typeCheckNot  :: Context -> [Expr] -> Maybe EType
typeCheckNot ctx es = do
    [e1] <- Just es
    t1 <- typeCheck ctx e1
    if t1 == TBool
        then Just TBool
        else Nothing

typeCheckComp  :: Context -> [Expr] -> Maybe EType
typeCheckComp ctx es = do
    [e1,e2] <- Just es
    t1 <- typeCheck ctx e1
    t2 <- typeCheck ctx e2
    if t1 == TNum && t2 == TNum
        then Just TBool
        else Nothing
