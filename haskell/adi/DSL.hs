module  DSL
    (   Expr 
    ,   eNum    -- :: Integer -> Expr
    ,   eBool   -- :: Bool -> Expr
    ,   eNat    -- :: Integer -> Expr
    ,   eZero   -- :: Expr
    ,   eSuc    -- :: Expr -> Expr
    ,   eVar    -- :: String -> Expr
    ,   eIf     -- :: Expr -> Expr -> Expr -> Expr
    ,   eLam    -- :: String -> Expr -> Expr
    ,   eApp    -- :: Expr -> Expr -> Expr
    ,   eRec    -- :: String -> Expr -> Expr
    ,   eCase   -- :: Expr -> Expr -> String -> Expr -> Expr
    ,   eAdd    -- :: Expr -> Expr -> Expr
    ,   eMul    -- :: Expr -> Expr -> Expr
    ,   eSub    -- :: Expr -> Expr -> Expr
    ,   eDiv    -- :: Expr -> Expr -> Expr
    ,   eAnd    -- :: Expr -> Expr -> Expr
    ,   eOr     -- :: Expr -> Expr -> Expr
    ,   eImp    -- :: Expr -> Expr -> Expr
    ,   eNot    -- :: Exor -> Expr
    ,   eLe     -- :: Expr -> Expr -> Expr
    ,   eEq     -- :: Expr -> Expr -> Expr
    )   where

import Op
import Syntax

eAdd :: Expr -> Expr -> Expr
eAdd e1 e2 = eOp oAdd [e1,e2]

eMul :: Expr -> Expr -> Expr
eMul e1 e2 = eOp oMul [e1,e2]

eSub :: Expr -> Expr -> Expr
eSub e1 e2 = eOp oSub [e1,e2]

eDiv :: Expr -> Expr -> Expr
eDiv e1 e2 = eOp oDiv [e1,e2]

eAnd :: Expr -> Expr -> Expr
eAnd e1 e2 = eOp oAnd [e1,e2]

eOr :: Expr -> Expr -> Expr
eOr e1 e2 = eOp oOr [e1,e2]

eImp :: Expr -> Expr -> Expr
eImp e1 e2 = eOp oImp [e1,e2]

eNot :: Expr -> Expr
eNot e1 = eOp oNot [e1]

eLe :: Expr -> Expr -> Expr
eLe e1 e2 = eOp oLe [e1,e2]

eEq :: Expr -> Expr -> Expr
eEq e1 e2 = eOp oEq [e1,e2]
