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

eAdd :: Expr
eAdd = eLam "x" (eLam "y" (eOp oAdd [eVar "x", eVar "y"]))

eMul :: Expr
eMul = eLam "x" (eLam "y" (eOp oMul [eVar "x", eVar "y"]))

eSub :: Expr
eSub = eLam "x" (eLam "y" (eOp oSub [eVar "x", eVar "y"]))

eDiv :: Expr
eDiv = eLam "x" (eLam "y" (eOp oDiv [eVar "x", eVar "y"]))

eAnd :: Expr
eAnd = eLam "x" (eLam "y" (eOp oAnd [eVar "x", eVar "y"]))

eOr :: Expr
eOr = eLam "x" (eLam "y" (eOp oOr [eVar "x", eVar "y"]))

eImp :: Expr
eImp = eLam "x" (eLam "y" (eOp oImp [eVar "x", eVar "y"]))

eNot :: Expr
eNot = eLam "x" (eOp oNot [eVar "x"])

eLe :: Expr
eLe = eLam "x" (eLam "y" (eOp oLe [eVar "x", eVar "y"]))

eEq :: Expr
eEq = eLam "x" (eLam "y" (eOp oEq [eVar "x", eVar "y"]))

eApp2 :: Expr -> Expr -> Expr -> Expr
eApp2 f x y = eApp (eApp f x) y

eFac :: Expr
eFac = (eRec "f" (eLam "n"
    (eIf (eApp2 eLe (eVar "n") (eNum 0)) 
        (eNum 1) 
        (eApp2 eMul 
            (eVar "n") 
            (eApp (eVar "f") 
                (eApp2 eSub (eVar "n") (eNum 1)))))))

eToNat :: Expr
eToNat = (eRec "f" (eLam "n"
    (eIf (eApp2 eLe (eVar "n") (eNum 0))
        eZero
        (eSuc 
            (eApp (eVar "f") 
                (eApp2 eSub (eVar "n") (eNum 1)))))))

eNat :: Integer -> Expr
eNat n = eApp eToNat (eNum n)

eFromNat :: Expr
eFromNat = (eRec "f" (eLam "n"
    (eCase (eVar "n") 
        (eNum 0)
        "n" (eApp2 eAdd 
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
