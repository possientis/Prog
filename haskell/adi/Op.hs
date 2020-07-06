{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE KindSignatures #-}

module  Op
    (   Op
    ,   PrimValue
    ,   Prim_   (..)
    ,   add
    ,   mul
    ,   sub
    ,   dvd
    ,   deltaPrim
    ,   opType      -- remove
    ,   deltaBool   -- remove
    ,   deltaNum    -- remove
    )   where

import Data.Functor.Const
import Data.Functor.Identity

data Prim_ f 
    = PNum  (f Integer) 
    | PBool (f Bool)

type PrimValue = Prim_ Identity
type PrimType  = Prim_ (Const ())

data OpType = OpType
    { argType :: [PrimType]
    , _retType ::  PrimType
    }

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

-- TODO
deltaPrim :: Op -> [PrimValue] -> PrimValue
deltaPrim op pvs = if length pvs /= length pts then
    error $  show op 
          ++ ": Wrong number of arguments in primitive call. Expecting "
          ++ show m
          ++ " arguments but received " 
          ++ show n
          ++ "."
    else PNum $ Identity $ deltaNum op n1 n2            -- TODO

    where
    m   = length pts
    n   = length pvs
    pts = argType . opType $ op  
    [PNum (Identity n1) , PNum (Identity n2)] = pvs     -- TODO

opType :: Op -> OpType
opType = \case 
    OpAdd -> OpType [tNum, tNum] tNum
    OpMul -> OpType [tNum, tNum] tNum
    OpSub -> OpType [tNum, tNum] tNum
    OpDiv -> OpType [tNum, tNum] tNum
    OpAnd -> OpType [tBool, tBool] tBool
    OpOr  -> OpType [tBool, tBool] tBool
    OpImp -> OpType [tBool, tBool] tBool

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

add :: Op
add = OpAdd

mul :: Op
mul = OpMul

sub :: Op
sub = OpSub

dvd :: Op
dvd = OpDiv

tNum :: PrimType 
tNum = PNum (Const ())

tBool :: PrimType
tBool = PNum (Const ())
