{-# LANGUAGE LambdaCase #-}

module  Op
    (   Op
    ,   add
    ,   mul
    ,   delta
    )   where

data Op = OpAdd | OpMul

instance Show Op where
   show = \case
        OpAdd -> "+"
        OpMul -> "*"

add :: Op
add = OpAdd

mul :: Op
mul = OpMul

delta :: Op -> Integer -> Integer -> Integer
delta = \case
    OpAdd   -> (+)
    OpMul   -> (*)
