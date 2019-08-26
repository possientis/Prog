{-# LANGUAGE DeriveDataTypeable     #-}
module  Expr 
    (   Expr    (..)
    ,   Binop   (..)
    ,   eval
    )   where

import Data.Generics

data Expr = ELitInt   Integer
          | EBinop    Binop   Expr Expr
          | EAntiInt  String
          | EAntiExpr String 

data Binop = OpAdd | OpSub | OpMul | OpDiv
    deriving (Show, Typeable, Data)

eval :: Expr -> Integer
eval (ELitInt n)     = n
eval (EBinop op x y) = (opToFun op) (eval x) (eval y)
eval _               = error "Evaluation of antiquotes not supported"

opToFun :: Binop -> Integer -> Integer -> Integer
opToFun OpAdd = (+)
opToFun OpSub = (-)
opToFun OpMul = (*)
opToFun OpDiv = div

