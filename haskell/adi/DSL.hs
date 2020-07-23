module  DSL
    (   Expr 
    ,   eNum        -- :: Integer -> Expr
    ,   eBool       -- :: Bool -> Expr
    ,   eNat        -- :: Integer -> Expr
    ,   eZero       -- :: Expr
    ,   eSuc        -- :: Expr -> Expr
    ,   eVar        -- :: String -> Expr
    ,   eIf         -- :: Expr -> Expr -> Expr -> Expr
    ,   eLam        -- :: String -> Expr -> Expr
    ,   eApp        -- :: Expr -> Expr -> Expr
    ,   eApp2       -- :: Expr -> Expr -> Expr -> Expr
    ,   eRec        -- :: String -> Expr -> Expr
    ,   eCase       -- :: Expr -> Expr -> String -> Expr -> Expr
    ,   eAdd        -- :: Expr
    ,   eMul        -- :: Expr
    ,   eSub        -- :: Expr
    ,   eDiv        -- :: Expr
    ,   eAnd        -- :: Expr
    ,   eOr         -- :: Expr
    ,   eImp        -- :: Expr
    ,   eNot        -- :: Expr
    ,   eLe         -- :: Expr
    ,   eEq         -- :: Expr
    ,   eFac        -- :: Expr
    ,   eToNat      -- :: Expr
    ,   eFromNat    -- :: Expr
    ,   eAddNat     -- :: Expr
    ,   eMulNat     -- :: Expr
    )   where

import Op
import Syntax

eAdd :: Expr -> Expr -> Expr
eAdd e1 e2 = eOp oAdd [e1, e2]

eMul :: Expr -> Expr -> Expr
eMul e1 e2 = eOp oMul [e1, e2]

eSub :: Expr -> Expr -> Expr
eSub e1 e2 = eOp oSub [e1, e2]

eDiv :: Expr -> Expr -> Expr
eDiv e1 e2 = eOp oDiv [e1, e2]

eAnd :: Expr -> Expr -> Expr
eAnd e1 e2 = eOp oAnd [e1, e2]

eOr :: Expr -> Expr -> Expr
eOr e1 e2 = eOp oOr [e1, e2]

eImp :: Expr -> Expr -> Expr
eImp e1 e2 = eOp oImp [e1, e2]

eNot :: Expr -> Expr
eNot e1 = eOp oNot [e1]

eLe :: Expr -> Expr -> Expr
eLe e1 e2 = eOp oLe [e1, e2]

eEq :: Expr -> Expr -> Expr
eEq e1 e2 = eOp oEq [e1, e2]

eApp2 :: Expr -> Expr -> Expr -> Expr
eApp2 f x y = eApp (eApp f x) y

eFac :: Expr
eFac = (eRec "f" (eLam "n"
    (eIf (eLe (eVar "n") (eNum 0)) 
        (eNum 1) 
        (eMul 
            (eVar "n") 
            (eApp (eVar "f") 
                (eSub (eVar "n") (eNum 1)))))))

eToNat :: Expr
eToNat = (eRec "f" (eLam "n"
    (eIf (eLe (eVar "n") (eNum 0))
        eZero
        (eSuc 
            (eApp (eVar "f") 
                (eSub (eVar "n") (eNum 1)))))))

eNat :: Integer -> Expr
eNat n = eApp eToNat (eNum n)

eFromNat :: Expr
eFromNat = (eRec "f" (eLam "n"
    (eCase (eVar "n") 
        (eNum 0)
        "n" (eAdd 
                (eNum 1) 
                (eApp (eVar "f") (eVar "n")))))) 

eAddNat :: Expr
eAddNat = (eRec "+" (eLam "n" (eLam "m"
    (eCase (eVar "n")
        (eVar "m")
        "n" (eSuc 
                (eApp2 (eVar "+") 
                    (eVar "n") 
                    (eVar "m")))))))

eMulNat :: Expr
eMulNat = (eRec "*" (eLam "n" (eLam "m"
    (eCase (eVar "n")
        eZero
        "n" (eApp2 eAddNat 
                (eVar "m") 
                (eApp2 (eVar "*") 
                    (eVar "n") 
                    (eVar "m")))))))
