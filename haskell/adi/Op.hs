{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE KindSignatures #-}

module  Op
    (   Op
    ,   add
    ,   mul
    ,   sub
    ,   dvd
    ,   deltaNum
    ,   deltaBool
    ,   toType
    )   where

data Typ = TNum | TBool

data Op = OpAdd 
        | OpMul 
        | OpSub 
        | OpDiv
        | OpAnd
        | OpOr
        | OpImp 

instance Show Op where
   show = \case
        OpAdd -> "+"
        OpMul -> "*"
        OpSub -> "-"
        OpDiv -> "/"
        OpAnd -> "/\\"
        OpOr  -> "\\/"
        OpImp -> "=>"

toType :: Op -> Typ
toType = \case 
    OpAdd -> TNum
    OpMul -> TNum
    OpSub -> TNum
    OpDiv -> TNum
    OpAnd -> TBool
    OpOr  -> TBool
    OpImp -> TBool

add :: Op
add = OpAdd

mul :: Op
mul = OpMul

sub :: Op
sub = OpSub

dvd :: Op
dvd = OpDiv

deltaNum :: Op -> Integer -> Integer -> Integer
deltaNum = \case
    OpAdd   -> (+)
    OpMul   -> (*)
    OpSub   -> (-)
    OpDiv   -> div
    _       -> error "deltaNum: illegal operator"

deltaBool :: Op -> Bool -> Bool -> Bool
deltaBool = \case
    OpAnd   -> (&&)
    OpOr    -> (||)
    OpImp   -> (\x y -> not x || y)
    _       -> error "deltaBool: illegal operator" 
