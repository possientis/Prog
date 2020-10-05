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
typeCheckOp = undefined

typeCheckIf :: Context -> Expr -> Expr -> Expr -> Maybe EType
typeCheckIf = undefined

typeCheckLam :: Context -> Var -> Expr -> Maybe EType
typeCheckLam = undefined

typeCheckApp :: Context -> Expr -> Expr -> Maybe EType
typeCheckApp = undefined

typeCheckRec :: Context -> Var -> Expr -> Maybe EType
typeCheckRec = undefined

typeCheckSuc :: Context -> Expr -> Maybe EType
typeCheckSuc = undefined

typeCheckCase :: Context -> Expr -> Expr -> Var -> Expr -> Maybe EType
typeCheckCase = undefined

