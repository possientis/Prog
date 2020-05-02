module  Op
    (   Op
    ,   add
    ,   mul
    )   where

data Op = OpAdd | OpMul

add :: Op
add = OpAdd

mul :: Op
mul = OpMul
