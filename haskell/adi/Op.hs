{-# LANGUAGE LambdaCase #-}

module  Op
    (   Op
    ,   add
    ,   mul
    ,   sub
    ,   dvd
    ,   delta
    )   where

data Op = OpAdd | OpMul | OpSub | OpDiv

instance Show Op where
   show = \case
        OpAdd -> "+"
        OpMul -> "*"
        OpSub -> "-"
        OpDiv -> "/"

add :: Op
add = OpAdd

mul :: Op
mul = OpMul

sub :: Op
sub = OpSub

dvd :: Op
dvd = OpDiv

delta :: Op -> Integer -> Integer -> Integer
delta = \case
    OpAdd   -> (+)
    OpMul   -> (*)
    OpSub   -> (-)
    OpDiv   -> div
