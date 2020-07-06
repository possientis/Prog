{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Op
    (   Op
    ,   PrimValue
    ,   Prim_   (..)
    ,   add
    ,   mul
    ,   sub
    ,   dvd
    ,   deltaPrim
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

instance Eq PrimType where
    (==) (PNum _)  (PNum _)  = True
    (==) (PBool _) (PBool _) = True
    (==) _         _         = False

instance Show PrimType where
    show (PNum _)  = "Integer"
    show (PBool _) = "Bool"

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
deltaPrim op pvs = case checkArgs op pvs of
    Left err  -> error err
    Right pvs' -> PNum $ Identity $ deltaNum op n1 n2   
        where
        [PNum (Identity n1) , PNum (Identity n2)] = pvs'

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

checkArgs :: Op -> [PrimValue] -> Either String [PrimValue]
checkArgs op pvs = if n /= m then
    Left $ "Type Error: In primitive call to " 
         ++ show op 
         ++ ", expecting "
         ++ show m
         ++ " arguments but received " 
         ++ show n
         ++ "."
    else mapM (checkArg op) $ zip (zip pvs pts) [1..]
    where
    m   = length pts
    n   = length pvs
    pts = argType . opType $ op  

-- Op and Int are needed for error message only
checkArg :: Op -> ((PrimValue,PrimType),Int) -> Either String PrimValue 
checkArg op ((pv,pt),n)
    | typeOf pv == pt   = Right pv
    | otherwise         = 
        Left $ "Type Error: In primitive call to " 
             ++ show op
             ++ ", argument n. "
             ++ show n
             ++ " is expected to be of type "
             ++ show pt
             ++ " but is of type "
             ++ show (typeOf pv)
             ++ "."
    
typeOf :: PrimValue -> PrimType
typeOf = \case
    PNum _  -> tNum
    PBool _ -> tBool

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
tBool = PBool (Const ())
