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
    ,   oAdd
    ,   oMul
    ,   oSub
    ,   oDiv
    ,   oAnd
    ,   oOr
    ,   oImp
    ,   oNot
    ,   oLe
    ,   oEq
    ,   deltaPrim
    )   where

import Data.Functor.Const
import Data.Functor.Identity

import Error

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

data OpData = OpData
    { opTypes :: [PrimType]
    , opImpl  :: [PrimValue] -> Either Error PrimValue
    }

data Op = OpAdd 
        | OpMul 
        | OpSub 
        | OpDiv
        | OpAnd
        | OpOr
        | OpImp 
        | OpNot
        | OpLe
        | OpEq
    deriving (Eq)

instance Show Op where
   show = \case
        OpAdd -> "+"
        OpMul -> "*"
        OpSub -> "-"
        OpDiv -> "/"
        OpAnd -> "/\\"
        OpOr  -> "\\/"
        OpImp -> "=>"
        OpNot -> "¬"
        OpLe  -> "<="
        OpEq  -> "=="

deltaPrim :: Op -> [PrimValue] -> Either Error PrimValue
deltaPrim op pvs = case checkArgs op pvs of
    Left e  -> Left $ (mkError $ "deltaPrim error:") <> e
    Right pvs' -> opImpl (opData op) pvs'

opData :: Op -> OpData
opData = \case 
    OpAdd -> OpData [tNum, tNum]   (deltaNum  OpAdd)
    OpMul -> OpData [tNum, tNum]   (deltaNum  OpMul)
    OpSub -> OpData [tNum, tNum]   (deltaNum  OpSub)
    OpDiv -> OpData [tNum, tNum]   (deltaNum  OpDiv)
    OpAnd -> OpData [tBool, tBool] (deltaBool OpAnd)
    OpOr  -> OpData [tBool, tBool] (deltaBool OpOr)
    OpImp -> OpData [tBool, tBool] (deltaBool OpImp)
    OpNot -> OpData [tBool]        (deltaNot  OpNot)
    OpLe  -> OpData [tNum, tNum]   (deltaComp OpLe)
    OpEq  -> OpData [tNum, tNum]   (deltaComp OpEq)

deltaNum :: Op -> [PrimValue] -> Either Error PrimValue
deltaNum op pvs = PNum . Identity  <$> deltaNum_ op n1 n2 where
    [PNum (Identity n1) , PNum (Identity n2)] = pvs
    
deltaBool :: Op -> [PrimValue] -> Either Error PrimValue 
deltaBool op pvs = Right . PBool . Identity $ deltaBool_ op b1 b2 where
    [PBool (Identity b1) , PBool (Identity b2)] = pvs

deltaNot :: Op -> [PrimValue] -> Either Error PrimValue
deltaNot op pvs = Right . PBool . Identity $ deltaNot_ op b where
    [PBool (Identity b)] = pvs

deltaComp :: Op -> [PrimValue] -> Either Error PrimValue
deltaComp op pvs = Right . PBool . Identity $ deltaComp_ op n1 n2 where
    [PNum (Identity n1) , PNum (Identity n2)] = pvs

checkArgs :: Op -> [PrimValue] -> Either Error [PrimValue]
checkArgs op pvs = if n /= m then
    Left $ mkError $ "Type Error: In primitive call to " 
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
    pts = opTypes . opData $ op  

-- Op and Int are needed for error message only
checkArg :: Op -> ((PrimValue,PrimType),Int) -> Either Error PrimValue 
checkArg op ((pv,pt),n)
    | typeOf pv == pt   = Right pv
    | otherwise         = 
        Left $ mkError $ "Type Error: In primitive call to " 
             ++ show op
             ++ ", argument n. "
             ++ show n
             ++ " is expected to be of type "
             ++ show pt
             ++ " but is of type "
             ++ show (typeOf pv)
             ++ "."

deltaNum_ :: Op -> Integer -> Integer -> Either Error Integer
deltaNum_ = \case
    OpAdd   -> \n m -> Right $ n + m
    OpMul   -> \n m -> Right $ n * m
    OpSub   -> \n m -> Right $ n - m
    OpDiv   -> \n m -> if m == 0
        then Left  $ mkError $ "Divide by 0 error"
        else Right $ div n m  
    _       -> error "deltaNum: illegal operator"

deltaBool_ :: Op -> Bool -> Bool -> Bool
deltaBool_ = \case
    OpAnd   -> (&&)
    OpOr    -> (||)
    OpImp   -> (\x y -> not x || y)
    _       -> error "deltaBool: illegal operator" 

deltaNot_ :: Op -> Bool -> Bool
deltaNot_ = \case
    OpNot   -> not
    _       -> error "deltaNot: illegal operator"

deltaComp_ :: Op -> Integer -> Integer -> Bool
deltaComp_ = \case
    OpLe    -> (<=)
    OpEq    -> (==)
    _       -> error "deltaComp: illegal operator"

typeOf :: PrimValue -> PrimType
typeOf = \case
    PNum _  -> tNum
    PBool _ -> tBool

tNum :: PrimType 
tNum = PNum (Const ())

tBool :: PrimType
tBool = PBool (Const ())

oAdd :: Op
oAdd = OpAdd

oMul :: Op
oMul = OpMul

oSub :: Op
oSub = OpSub

oDiv :: Op
oDiv = OpDiv

oAnd :: Op
oAnd = OpAnd

oImp :: Op
oImp = OpImp

oOr :: Op
oOr = OpOr

oNot :: Op
oNot = OpNot

oLe :: Op
oLe = OpLe

oEq :: Op
oEq = OpEq
