module ZF.Expr
  ( Expr  (..)
  , eAnd
  , eExists
  , eOr
  , eNot
  , (===)
  ) where

import ZF.Var

data Expr
  = EVar Var 
  | Bot
  | In Var Var
  | Imp Expr Expr
  | All Var Expr
  | PLam Var Expr
  | PApp Expr Expr
  | SLam Var Expr
  | SApp Expr Expr

(==>) :: Expr -> Expr -> Expr
(==>) = Imp

pApp :: Expr -> Expr -> Expr -> Expr
pApp op e1 e2 = PApp (PApp op e1) e2

sApp :: Expr -> Expr -> Expr -> Expr
sApp op e1 e2 = SApp (SApp op e1) e2

eLamNot :: Expr
eLamNot = PLam p $ (EVar p) ==> Bot

eNot :: Expr -> Expr
eNot = PApp eLamNot

eLamOr :: Expr
eLamOr = PLam p $ PLam q $ eNot (EVar p) ==> (EVar q)

eOr :: Expr -> Expr -> Expr
eOr = pApp eLamOr

eLamAnd :: Expr
eLamAnd = PLam p $ PLam q $ eNot $ eOr (eNot $ EVar p) (eNot $ EVar q)

eAnd :: Expr -> Expr -> Expr
eAnd = pApp eLamAnd

eLamEqual :: Expr
eLamEqual = SLam x $ SLam y $ 
  eAnd (All z $ In z x ==> In z y) $
  eAnd (All z $ In z y ==> In z x) $ 
  eAnd (All z $ In x z ==> In y z) $ 
       (All z $ In y z ==> In x z)

(===) :: Expr -> Expr -> Expr
(===) = sApp eLamEqual

eLamExists :: Expr
eLamExists = SLam x $ PLam p $ eNot $ All x $ eNot (EVar p)

eExists :: Var -> Expr -> Expr
eExists v e = PApp (SApp eLamExists (EVar v)) e
